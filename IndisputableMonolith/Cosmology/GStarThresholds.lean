import Mathlib
import IndisputableMonolith.StandardModel.RelativisticDOF

/-!
# g_star(T): Temperature-Dependent Relativistic Degrees of Freedom

STATUS TAG: **MODEL (instantaneous-threshold step function) over adopted
SM content**. Built 2026-07-02 in response to the external review point
"g_star is temperature dependent, but RS fixes one number ... the
repository does not implement a function g_star(T), threshold decoupling,
finite-temperature equations of state, or epoch-dependent particle
content."

This module implements the standard threshold-decoupling step function
g_star(T): each species contributes its full relativistic degree count
while T exceeds its mass threshold and drops out below it, with the QCD
confinement transition at T_QCD ≈ 0.15 GeV switching the strong sector
from quark–gluon plasma content (gluons + u,d,s) to hadronic content
(pions). All arithmetic is exact over ℚ and machine-checked.

## Honest scope

- The step function is the standard leading approximation. It does NOT
  implement Boltzmann-suppressed tails near thresholds, the lattice QCD
  equation of state through the crossover, or the neutrino-decoupling
  reheating factor (4/11)^(4/3) below e⁺e⁻ annihilation. Valid domain:
  T ≳ 1 MeV (above neutrino decoupling).
- Mass thresholds are IMPORTED (PDG rounded values, rational
  approximations). RS's φ-ladder mass modules (IndisputableMonolith.Masses)
  predict these masses independently; this module does not re-derive them,
  it uses them as ordering thresholds only (only the relative order of
  T vs. m matters for the step counts, so rounding is harmless).
- Particle content per species is the same imported SM bookkeeping as
  StandardModel.RelativisticDOF (see its header for the RS-derived vs.
  imported split: gauge group and generation count RS-derived; matter
  representations, neutrino convention, and the 7/8 integral imported).
- Below T_EW the bosonic sector is counted in the broken phase (massive
  W/Z with 3 polarizations, 1 physical Higgs); above T_EW the symmetric
  phase (massless W/Z with 2 polarizations, 4 Higgs-doublet DOF) has the
  SAME total (28), so the high-T evaluation matches
  RelativisticDOF.g_star_derived exactly (bridge theorem below).

## Spot checks proved below (standard textbook values)

| T          | epoch                        | g_star  |
|------------|------------------------------|---------|
| 200 GeV    | all SM relativistic          | 106.75  |
| 10 GeV     | after t, H, Z, W decouple    | 86.25   |
| 1 GeV      | after b, τ, c decouple       | 61.75   |
| 0.14 GeV   | below T_QCD (π, μ, e, ν, γ)  | 17.25   |
| 2 MeV      | after π, μ annihilate        | 10.75   |

## Main results

- `g_star (T : ℚ) : ℚ` — the step function.
- `g_star_high_matches_derived` — at high T it equals the fixed 106.75
  of StandardModel.RelativisticDOF (so the old fixed number is now the
  high-T evaluation of a real function, not a free-standing constant).
- `g_star_steps_antitone_chain` — the sampled epochs decrease as the
  universe cools.
- `g_star_dirac_high` — the thermalized-Dirac-neutrino branch gives 112
  at high T (the neutrino convention carried as an explicit input).

## Status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith
namespace Cosmology
namespace GStarThresholds

/-- A thermal species: name, mass threshold (GeV, rational approximation;
    only its order relative to T matters), internal degrees of freedom,
    and quantum statistics. -/
structure Species where
  name : String
  mass : ℚ
  dof : ℕ
  fermion : Bool
deriving Repr

/-! ## Species tables (imported SM content; masses PDG-rounded) -/

/-- Photon: massless, 2 polarizations. -/
def photon : Species := ⟨"photon", 0, 2, false⟩

/-- Neutrinos, minimal-SM convention: 3 generations × (LH ν + RH ν̄) = 6. -/
def neutrinos : Species := ⟨"neutrinos (3 gen, minimal)", 0, 6, true⟩

/-- Neutrinos, thermalized-Dirac branch: 3 generations × 4 = 12. -/
def neutrinos_dirac : Species := ⟨"neutrinos (3 gen, Dirac, RH thermalized)", 0, 12, true⟩

/-- Top quark: m ≈ 173 GeV, 12 DOF (3 color × 2 spin × 2 p/ap). -/
def top : Species := ⟨"top", 173, 12, true⟩

/-- Higgs boson (broken phase): m ≈ 125 GeV, 1 DOF. -/
def higgs : Species := ⟨"Higgs", 125, 1, false⟩

/-- Z boson (broken phase): m ≈ 91.2 GeV, 3 polarizations. -/
def zboson : Species := ⟨"Z", 456/5, 3, false⟩

/-- W± bosons (broken phase): m ≈ 80.4 GeV, 2 × 3 polarizations = 6. -/
def wboson : Species := ⟨"W±", 402/5, 6, false⟩

/-- Bottom quark: m ≈ 4.2 GeV, 12 DOF. -/
def bottom : Species := ⟨"bottom", 21/5, 12, true⟩

/-- Tau lepton: m ≈ 1.777 GeV, 4 DOF. -/
def tau : Species := ⟨"tau", 1777/1000, 4, true⟩

/-- Charm quark: m ≈ 1.27 GeV, 12 DOF. -/
def charm : Species := ⟨"charm", 127/100, 12, true⟩

/-- Muon: m ≈ 0.1057 GeV, 4 DOF. -/
def muon : Species := ⟨"muon", 1057/10000, 4, true⟩

/-- Electron: m ≈ 0.000511 GeV, 4 DOF. -/
def electron : Species := ⟨"electron", 511/1000000, 4, true⟩

/-- Gluons (deconfined, T > T_QCD): 8 × 2 = 16 DOF. -/
def gluons : Species := ⟨"gluons", 0, 16, false⟩

/-- Up quark (deconfined; current mass ≪ T_QCD): 12 DOF. -/
def up : Species := ⟨"up", 0, 12, true⟩

/-- Down quark (deconfined): 12 DOF. -/
def down : Species := ⟨"down", 0, 12, true⟩

/-- Strange quark (deconfined; m_s ≈ 95 MeV < T_QCD): 12 DOF. -/
def strange : Species := ⟨"strange", 0, 12, true⟩

/-- Pions π⁺, π⁻, π⁰ (confined phase): m ≈ 0.135–0.140 GeV, 3 DOF. -/
def pions : Species := ⟨"pions", 27/200, 3, false⟩

/-- QCD confinement threshold: T_QCD ≈ 0.15 GeV. Above it the strong
    sector is quark–gluon plasma; below it, hadrons. IMPORTED (lattice
    QCD crossover scale, rounded); the instantaneous switch is the step
    approximation, not the real crossover equation of state. -/
def T_qcd : ℚ := 3/20

/-- Electroweak-sector species with mass thresholds (decouple as T falls). -/
def ew_species : List Species :=
  [top, higgs, zboson, wboson, bottom, tau, charm, muon, electron]

/-- Strong-sector species above T_QCD (quark–gluon plasma). -/
def qgp_species : List Species := [gluons, up, down, strange]

/-- Strong-sector species below T_QCD (hadronic phase). -/
def hadron_species : List Species := [pions]

/-! ## The step function -/

/-- Energy-density weight of one species: DOF, times 7/8 for fermions
    (sign from spin-statistics, RS-derived; integral value 7/8 imported —
    see StandardModel.RelativisticDOF.fermi_dirac_weight). -/
def species_g (s : Species) : ℚ :=
  if s.fermion then (7 : ℚ) / 8 * s.dof else s.dof

/-- Species relativistic and populated at temperature T (GeV), with the
    neutrino sector supplied as an explicit input (minimal vs. Dirac). -/
def activeWith (nu : Species) (T : ℚ) : List Species :=
  [photon, nu]
    ++ ew_species.filter (fun s => s.mass < T)
    ++ (if T_qcd < T then qgp_species
        else hadron_species.filter (fun s => s.mass < T))

/-- g_star(T) with an explicit neutrino-sector input. -/
def g_starWith (nu : Species) (T : ℚ) : ℚ :=
  ((activeWith nu T).map species_g).sum

/-- **g_star(T)**: the temperature-dependent relativistic degree count,
    minimal-SM neutrino convention. Instantaneous-threshold step model;
    valid for T ≳ 1 MeV. -/
def g_star (T : ℚ) : ℚ := g_starWith neutrinos T

/-! ## Evaluation theorems (exact rational arithmetic) -/

/-- T = 200 GeV: all SM species relativistic → 427/4 = 106.75. -/
theorem g_star_high : g_star 200 = 427/4 := by native_decide

/-- T = 10 GeV: t, H, Z, W decoupled → 345/4 = 86.25. -/
theorem g_star_10GeV : g_star 10 = 345/4 := by native_decide

/-- T = 1 GeV: b, τ, c also decoupled → 247/4 = 61.75. -/
theorem g_star_1GeV : g_star 1 = 247/4 := by native_decide

/-- T = 0.14 GeV (just below T_QCD): γ, π, μ, e, ν → 69/4 = 17.25. -/
theorem g_star_140MeV : g_star (7/50) = 69/4 := by native_decide

/-- T = 2 MeV (above neutrino decoupling; π, μ gone): γ, e, ν
    → 43/4 = 10.75. -/
theorem g_star_2MeV : g_star (1/500) = 43/4 := by native_decide

/-- The sampled epochs decrease monotonically as the universe cools:
    10.75 < 17.25 < 61.75 < 86.25 < 106.75. -/
theorem g_star_steps_antitone_chain :
    g_star (1/500) < g_star (7/50) ∧
    g_star (7/50) < g_star 1 ∧
    g_star 1 < g_star 10 ∧
    g_star 10 < g_star 200 := by native_decide

/-! ## Bridge to the fixed high-T constant -/

/-- The fixed 106.75 used across the cosmology modules is the high-T
    evaluation of g_star(T): the old constant is now a function value,
    not a free-standing number. -/
theorem g_star_high_matches_derived :
    ((g_star 200 : ℚ) : ℝ) = StandardModel.RelativisticDOF.g_star_derived := by
  rw [g_star_high, StandardModel.RelativisticDOF.g_star_derived_eq]
  norm_num

/-! ## The Dirac-neutrino branch (explicit model input) -/

/-- With thermalized right-handed Dirac neutrinos, the high-T count is
    112, not 106.75 (matches RelativisticDOF.g_star_dirac_eq). The
    neutrino convention is a real input that moves the answer. -/
theorem g_star_dirac_high : g_starWith neutrinos_dirac 200 = 112 := by
  native_decide

/-- The two neutrino conventions agree everywhere except through the
    neutrino term: the branch gap at high T is (7/8)·6 = 21/4 = 5.25. -/
theorem g_star_branch_gap_high :
    g_starWith neutrinos_dirac 200 - g_star 200 = 21/4 := by native_decide

end GStarThresholds
end Cosmology
end IndisputableMonolith
