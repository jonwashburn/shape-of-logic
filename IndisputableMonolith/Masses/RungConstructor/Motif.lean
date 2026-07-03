import Mathlib
import IndisputableMonolith.Masses.RungConstructor.Basic

namespace IndisputableMonolith
namespace Masses
namespace RungConstructor

/-! ## Generation Step Constants

### Sector-Dependent Generation Torsion (SDGT)

Each fermion sector uses different cube cell counts for its generation steps.
The four step values form a cyclic chain:

  V+F-C=13 → E_pass=11 → F=6 → V=8

Each sector takes two consecutive values:
- Up quarks:   {V+F-C=13, E_pass=11}, total = 2E = 24
- Leptons:     {E_pass=11, F=6},       total = W = 17
- Down quarks: {F=6, V=8},             total = V+F = 14

The three spans partition N₃ = 2D^D + 1 = 55.
Lean proof: `IndisputableMonolith.Masses.SectorDependentTorsion`

### Legacy (universal torsion, leptons only)

The old convention used {0, 11, 17} for all charged fermions.
This is retained as `tau_charged` for backward compatibility but
is accurate only for leptons. Use `tau_sdgt` for quarks. -/

def step_gen1 : ℤ := 11
def step_gen2_charged : ℤ := 6
def step_gen2_neutrino : ℤ := 8

/-- Cumulative generation torsion for leptons (legacy name: tau_charged).
    CORRECT for leptons. For quarks, use tau_sdgt. -/
def tau_charged (gen : ℕ) : ℤ :=
  match gen with
  | 0 => 0
  | 1 => step_gen1
  | _ => step_gen1 + step_gen2_charged  -- gen ≥ 2

/-- Cumulative generation torsion for neutrinos. -/
def tau_neutrino (gen : ℕ) : ℤ :=
  match gen with
  | 0 => 0
  | 1 => step_gen1
  | _ => step_gen1 + step_gen2_neutrino  -- gen ≥ 2

/-! ### SDGT: Sector-specific generation torsion (HYPOTHESIS for quarks)

These quark-sector torsion values were identified from PDG same-scale
mass ratios, then matched to Q₃ cell counts. The integers ARE cube-geometric
(Lean-proved), but the assignment of specific integers to specific sectors
is a HYPOTHESIS, not a first-principles derivation.

The lepton torsion {0, 11, 17} remains DERIVED (from edge/face geometry). -/

/-- Up-quark generation steps: {V+F-C=13, E_pass=11}. HYPOTHESIS. -/
def step_up_gen1 : ℤ := 13   -- V + F - C = 8 + 6 - 1
def step_up_gen2 : ℤ := 11   -- E_pass = E - A = 12 - 1

/-- Down-quark generation steps: {F=6, V=8}. HYPOTHESIS. -/
def step_down_gen1 : ℤ := 6   -- F = 2D = 6
def step_down_gen2 : ℤ := 8   -- V = 2^D = 8

/-- Sector-dependent cumulative generation torsion.
    CANONICAL for all fermion sectors. -/
def tau_sdgt (sector : Sector) (gen : ℕ) : ℤ :=
  match sector, gen with
  | _, 0           => 0
  | .Lepton, 1     => step_gen1                         -- 11 = E_pass
  | .Lepton, _     => step_gen1 + step_gen2_charged     -- 17 = W
  | .UpQuark, 1    => step_up_gen1                      -- 13 = V+F-C
  | .UpQuark, _    => step_up_gen1 + step_up_gen2       -- 24 = 2E
  | .DownQuark, 1  => step_down_gen1                    -- 6  = F
  | .DownQuark, _  => step_down_gen1 + step_down_gen2   -- 14 = V+F
  | .Neutrino, 1   => step_gen1                         -- 11
  | .Neutrino, _   => step_gen1 + step_gen2_neutrino    -- 19
  | .Electroweak, _ => 0

/-- Sector-global length baseline. -/
def ell_baseline : Sector → ℤ
  | .Lepton      => 2
  | .Neutrino    => 0
  | .UpQuark     => 4
  | .DownQuark   => 4
  | .Electroweak => 1

/-- Legacy rung constructor (universal torsion {0,11,17} for all charged).
    CORRECT for leptons and neutrinos. For quarks, use compute_rung_sdgt. -/
def compute_rung (s : Species) : ℤ :=
  match s with
  | .fermion f =>
      let sector := sectorOf (.fermion f)
      let gen := (RSBridge.genOf f).val
      match sector with
      | .Neutrino => ell_baseline sector + tau_neutrino gen
      | _         => ell_baseline sector + tau_charged gen
  | .W | .Z | .H =>
      ell_baseline .Electroweak

/-- SDGT rung constructor (sector-dependent torsion).
    Lepton rungs: DERIVED. Quark rungs: HYPOTHESIS (from PDG data). -/
def compute_rung_sdgt (s : Species) : ℤ :=
  match s with
  | .fermion f =>
      let sector := sectorOf (.fermion f)
      let gen := (RSBridge.genOf f).val
      ell_baseline sector + tau_sdgt sector gen
  | .W | .Z | .H =>
      ell_baseline .Electroweak

end RungConstructor
end Masses
end IndisputableMonolith
