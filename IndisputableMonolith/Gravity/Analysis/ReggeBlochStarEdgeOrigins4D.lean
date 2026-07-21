import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochOrbitTransport4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochFold4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochTransportedAllOrbit4D
import IndisputableMonolith.Gravity.Analysis.ReggeBlochAllOrbitSymbol4D
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DOrbitClassification

/-!
# Position-resolved star edge origins (fold repair)

Typed blocker `fold_position_resolved_star_phase` (2026-07-21).
Seed star edges carry lattice origins; covering perms transport both class
index and origin into the deficit phase for non-`t11` orbits.

Python gate: `scripts/qg/regge_4d_fold_position_resolved_20260721.py`
(banked gauges → 0; TT plus=cross=-1/4 on `symbolDir`; t11 untouched).

Does **not** flip `gap_action_recovery`. Forbidden: base0 half-repair.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeBlochStarEdgeOrigins4D

open BigOperators
open ReggeEdgeStencil4D
open ReggeBlochFold4D
open ReggeBlochOrbitTransport4D
open ReggeBlochTransportedAllOrbit4D
open ReggeBlochAllOrbitSymbol4D (isOrbit phaseScaleDir)
open ReggeHinge4DOrbitClassification

noncomputable section

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Wave4 := Fin 4 → ℝ

/-- One seed-frame star edge contribution: class index, weight, origin. -/
structure SeedEdgeContrib where
  cls : Fin 15
  weight : ℝ
  origin : Wave4

/-- Seed contributions for orbit seed `t12`. -/
def seedEdgeContribs_t12 : List SeedEdgeContrib :=
  [
    {
      cls := (5 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (3 : Fin 15)
      weight := ((2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 1, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (1 : Fin 15)
      weight := ((2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 1, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (0 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (6 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (2 : Fin 15)
      weight := ((2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (8 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (10 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (0 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (6 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (4 : Fin 15)
      weight := ((2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (8 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((1 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (12 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 2 / 4
      origin := fun i => ((![0, 0, 0, -1] : Fin 4 → ℤ) i : ℝ)
    }
  ]

theorem seedEdgeContribs_t12_length :
    seedEdgeContribs_t12.length = 22 := rfl

/-- Seed contributions for orbit seed `t13`. -/
def seedEdgeContribs_t13 : List SeedEdgeContrib :=
  [
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (3 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (1 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 1, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (1 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((-2 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((3 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 1] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (3 : Fin 15)
      weight := ((-6 : ℤ) : ℝ) * Real.sqrt 3 / 12
      origin := fun i => ((![1, 0, 0, 1] : Fin 4 → ℤ) i : ℝ)
    }
  ]

theorem seedEdgeContribs_t13_length :
    seedEdgeContribs_t13.length = 24 := rfl

/-- Seed contributions for orbit seed `t22`. -/
def seedEdgeContribs_t22 : List SeedEdgeContrib :=
  [
    {
      cls := (2 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (6 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (1 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (3 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (5 : Fin 15)
      weight := ((-4 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (2 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (10 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (1 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (13 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (9 : Fin 15)
      weight := ((-4 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (2 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (6 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (0 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (3 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (12 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (4 : Fin 15)
      weight := ((-4 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (2 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (14 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (10 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 0, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (11 : Fin 15)
      weight := ((-1 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (0 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (7 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![1, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (12 : Fin 15)
      weight := ((2 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    },
    {
      cls := (8 : Fin 15)
      weight := ((-4 : ℤ) : ℝ) / 4
      origin := fun i => ((![0, 1, 0, 0] : Fin 4 → ℤ) i : ℝ)
    }
  ]

theorem seedEdgeContribs_t22_length :
    seedEdgeContribs_t22.length = 32 := rfl

/-- Identity-transport complements (Lean `kernel21 = kernel12`, `kernel31 = kernel13`). -/
def seedEdgeContribs_t21 : List SeedEdgeContrib := seedEdgeContribs_t12
def seedEdgeContribs_t31 : List SeedEdgeContrib := seedEdgeContribs_t13

def seedEdgeContribs : HingeOrbitType → List SeedEdgeContrib
  | .t11 => []
  | .t12 => seedEdgeContribs_t12
  | .t21 => seedEdgeContribs_t21
  | .t13 => seedEdgeContribs_t13
  | .t31 => seedEdgeContribs_t31
  | .t22 => seedEdgeContribs_t22

/-- Transport a seed-frame origin by covering perm `p`. -/
def transportOrigin (p : Fin 24) (off : Wave4) : Wave4 :=
  fun i => ∑ j : Fin 4, if coordPermOf p j = i then off j else 0

/-- One contribution evaluated at a transported slot. -/
def edgeContribPhased (p : Fin 24) (base : Wave4) (H : Mat4) (m : Wave4)
    (c : SeedEdgeContrib) : ℝ :=
  c.weight *
    planeWaveClassPert H m
      (fun i => base i + transportOrigin p c.origin i) (permClass p c.cls)

/-- Position-resolved deficit phased class-dot from seed edge contributions. -/
def phasedDeficitDotEdgeOrigins (ty : HingeOrbitType) (H : Mat4)
    (m : Wave4) (s : Fin 24) (t : Fin 10) : ℝ :=
  ((seedEdgeContribs ty).map
    (edgeContribPhased (orbitCoveringPerm ty s t) (hingeBase s t) H m)).sum

private lemma list_sum_map_smul_planeWave (c : ℝ) (H : Mat4) (m : Wave4)
    (p : Fin 24) (base : Wave4) (cs : List SeedEdgeContrib) :
    (cs.map (fun e =>
        e.weight *
          planeWaveClassPert (c • H) m
            (fun i => base i + transportOrigin p e.origin i)
            (permClass p e.cls))).sum =
      c *
        (cs.map (fun e =>
            e.weight *
              planeWaveClassPert H m
                (fun i => base i + transportOrigin p e.origin i)
                (permClass p e.cls))).sum := by
  induction cs with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [planeWaveClassPert_smul, ih]
      ring

theorem phasedDeficitDotEdgeOrigins_smul (c : ℝ) (ty : HingeOrbitType)
    (H : Mat4) (m : Wave4) (s : Fin 24) (t : Fin 10) :
    phasedDeficitDotEdgeOrigins ty (c • H) m s t =
      c * phasedDeficitDotEdgeOrigins ty H m s t := by
  unfold phasedDeficitDotEdgeOrigins edgeContribPhased
  exact list_sum_map_smul_planeWave c H m (orbitCoveringPerm ty s t)
    (hingeBase s t) (seedEdgeContribs ty)

/-- Two-jet phase² sum for m² trunc: `Σ w_e c_d phase(origin_e, d)²`. -/
def edgeContribPhase2 (p : Fin 24) (base : Wave4) (H : Mat4) (dir : Wave4)
    (c : SeedEdgeContrib) : ℝ :=
  c.weight * classCoeff H (permClass p c.cls) *
    (phaseScaleDir dir (fun i => base i + transportOrigin p c.origin i)
      (permClass p c.cls)) ^ 2

def slotOrbitDeficitPhase2EdgeOrigins (ty : HingeOrbitType) (H : Mat4)
    (dir : Wave4) (s : Fin 24) (t : Fin 10) : ℝ :=
  ((seedEdgeContribs ty).map
    (edgeContribPhase2 (orbitCoveringPerm ty s t) (hingeBase s t) H dir)).sum

/-- Position-resolved m² trunc slot coefficient for non-`t11` orbits. -/
def m2OrbitSlotCoeffEdgeOrigins (ty : HingeOrbitType) (H : Mat4)
    (dir : Wave4) (s : Fin 24) (t : Fin 10) : ℝ :=
  if isOrbit ty s t then
    (∑ d : Fin 15, slotOrbitAreaCov ty s t d * classCoeff H d) *
      (-(1 / 2 : ℝ) * slotOrbitDeficitPhase2EdgeOrigins ty H dir s t)
  else 0

def m2OrbitMomentEdgeOrigins (ty : HingeOrbitType) (H : Mat4)
    (dir : Wave4) : ℝ :=
  ∑ s : Fin 24, ∑ t : Fin 10, m2OrbitSlotCoeffEdgeOrigins ty H dir s t

/-- Mixed fold: t11 keeps legacy transported m²; others use edge origins. -/
def m2AllOrbitMomentDistinctHingeEdgeOrigins (H : Mat4) (dir : Wave4) : ℝ :=
  (orbitStarSize .t11)⁻¹ * m2TransportedOrbitMoment .t11 H dir +
    (orbitStarSize .t12)⁻¹ * m2OrbitMomentEdgeOrigins .t12 H dir +
    (orbitStarSize .t21)⁻¹ * m2OrbitMomentEdgeOrigins .t21 H dir +
    (orbitStarSize .t13)⁻¹ * m2OrbitMomentEdgeOrigins .t13 H dir +
    (orbitStarSize .t31)⁻¹ * m2OrbitMomentEdgeOrigins .t31 H dir +
    (orbitStarSize .t22)⁻¹ * m2OrbitMomentEdgeOrigins .t22 H dir

structure StarEdgeOriginsStatus where
  tablesLanded : Bool
  gapActionRecovery : Bool
  base0Forbidden : Bool

def starEdgeOriginsStatus : StarEdgeOriginsStatus where
  tablesLanded := true
  gapActionRecovery := false
  base0Forbidden := true

theorem starEdgeOriginsStatus_flags :
    starEdgeOriginsStatus.tablesLanded = true ∧
      starEdgeOriginsStatus.gapActionRecovery = false ∧
        starEdgeOriginsStatus.base0Forbidden = true := by
  decide

end

end ReggeBlochStarEdgeOrigins4D
end Analysis
end Gravity
end IndisputableMonolith
