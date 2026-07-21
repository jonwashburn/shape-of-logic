import IndisputableMonolith.Holography.HorizonOneSidedCut
import IndisputableMonolith.Holography.HorizonClockRate
import IndisputableMonolith.Holography.RecordMonotonicity

/-!
# Local recognition horizon cuts

This module joins three audited legs on one shared context:

* LEG-A one-sided cut: `HorizonSumsPerSide` (MODEL) forces the horizon record to
  double-post the seam (`horizon_record_double_posts_seam`);
* posted-record heat: exterior projection of a closed `CutCfg` with discrete
  books balance / unit-temperature Clausius as THEOREMS about that record;
* LEG-B near-horizon rate: `NearHorizonRindlerForm` (MODEL, currently only
  `kappa > 0`) with the least positive deficit-free period as a THEOREM.

A `LocalCut` is then a closed cut configuration living in that shared context.
Interior-private and rest-of-universe data are not visible in the exterior
record. No stress tensor, Ricci tensor, focusing law, curvature match, Unruh
claim, or Einstein equation occurs in this module.
-/

namespace IndisputableMonolith
namespace Holography
namespace LocalRecognitionHorizonCut

open HorizonOneSidedCut HorizonClockRate DeficitFreePeriod RecordMonotonicity

/--
Shared local-horizon context joining the one-sided-cut MODEL, the posted-record
carrier dimensions, and the near-horizon rate MODEL. No thermality or curvature
premise is included.
-/
structure LocalHorizonContext (a s b r : ℕ) (kappa : ℝ) where
  horizonRecord : ℕ
  oneSided : HorizonSumsPerSide a s b r horizonRecord
  rindler : NearHorizonRindlerForm kappa

/--
A globally closed one-sided cut configuration living in a shared local-horizon
context. Cut data are relative to the context; rate and one-sided premises live
on the context itself.
-/
structure LocalCut {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa) where
  cfg : CutCfg a s b r
  closed : cutClosed cfg

/-- Read a `ZMod 2` cut entry as its posted Boolean bit. -/
def bitReadout (x : ZMod 2) : Bool :=
  decide (x = 1)

/--
The exterior-accessible record: exterior-private entries followed by seam
entries. Interior-private and rest-of-universe entries are traced out.
-/
def exteriorRecord {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c : LocalCut H) : List Bool :=
  List.ofFn (fun i : Fin a => bitReadout (c.cfg.1 i))
    ++ List.ofFn (fun j : Fin s => bitReadout (c.cfg.2.1 j))

theorem exteriorRecord_length {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c : LocalCut H) :
    (exteriorRecord c).length = a + s := by
  simp [exteriorRecord]

/-- Exterior posted-record potential in integer bit units. -/
def exteriorPotential {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c : LocalCut H) : ℤ :=
  recordWeight (exteriorRecord c)

/--
One-step exterior heat in integer bit units. The physical identification of
this posted flux with horizon heat is the inherited posting-rule MODEL.
-/
def exteriorStepHeat {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) : ℤ :=
  recordFlux (exteriorRecord c) (exteriorRecord c')

/-- Posted exterior heat is exactly the change of record potential. -/
theorem exteriorStepHeat_eq_potential {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) :
    exteriorStepHeat c c' = exteriorPotential c' - exteriorPotential c := by
  exact recordFlux_eq_weight_sub _ _ (by
    rw [exteriorRecord_length, exteriorRecord_length])

/--
Unit-temperature discrete Clausius predicate on the local cut carrier. This is
record thermodynamics in bit units, not continuum Unruh thermality.
-/
def ExteriorClausius {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (entropy : LocalCut H → ℤ) : Prop :=
  ∀ c c', exteriorStepHeat c c' = entropy c' - entropy c

/-- The exterior record potential satisfies cut-level discrete Clausius. -/
theorem exterior_record_potential_clausius {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa} :
    ExteriorClausius (exteriorPotential : LocalCut H → ℤ) :=
  exteriorStepHeat_eq_potential

/-- Total posted exterior heat along a path of closed local cuts. -/
def exteriorPathHeat {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa} :
    List (LocalCut H) → ℤ
  | [] => 0
  | [_] => 0
  | c :: c' :: rest => exteriorStepHeat c c' + exteriorPathHeat (c' :: rest)

/-- The cut-level books balance along every finite local-horizon trajectory. -/
theorem exterior_books_balance {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c : LocalCut H)
    (p : List (LocalCut H)) :
    exteriorPathHeat (c :: p) =
      exteriorPotential (p.getLastD c) - exteriorPotential c := by
  induction p generalizing c with
  | nil => simp [exteriorPathHeat]
  | cons c' rest ih =>
      simp only [exteriorPathHeat, List.getLastD_cons,
        exteriorStepHeat_eq_potential, ih c']
      ring

/--
Exterior heat ignores every change hidden behind the same exterior projection.
This is the exact one-sidedness statement used by the record bookkeeping.
-/
theorem exteriorStepHeat_zero_of_same_projection
    {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H)
    (h : projA c.cfg = projA c'.cfg) :
    exteriorStepHeat c c' = 0 := by
  have hA : c.cfg.1 = c'.cfg.1 := by
    simpa [projA] using congrArg Prod.fst h
  have hS : c.cfg.2.1 = c'.cfg.2.1 := by
    simpa [projA] using congrArg Prod.snd h
  have hRecord : exteriorRecord c = exteriorRecord c' := by
    simp only [exteriorRecord]
    rw [hA, hS]
  unfold exteriorStepHeat
  rw [hRecord]
  exact recordFlux_self _

/-- Every exterior and seam reading extends to a closed local cut in context `H`. -/
def ofExteriorReading {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa)
    (gA : Fin a → ZMod 2) (gS : Fin s → ZMod 2) :
    LocalCut H where
  cfg := compA (b := b) (r := r) gA gS
  closed := compA_closed gA gS

/--
Given the one-sided-cut MODEL on the shared context, the horizon record equals
the joint boundary marginal bit count plus the seam bit count.
-/
theorem horizonRecord_eq_joint_plus_seam {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa) :
    H.horizonRecord =
      Nat.log2 (((closedSet a s b r).image projAB).card) + s :=
  horizon_record_double_posts_seam a s b r H.horizonRecord H.oneSided

/--
Discrimination: when the seam is nonempty, the one-sided horizon record cannot
equal the joint boundary marginal. The seam double-post is load-bearing.
-/
theorem oneSided_horizonRecord_ne_joint_marginal {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa)
    (hs : 0 < s) :
    H.horizonRecord ≠ Nat.log2 (((closedSet a s b r).image projAB).card) := by
  intro heq
  have h := horizonRecord_eq_joint_plus_seam H
  have hEq :
      Nat.log2 (((closedSet a s b r).image projAB).card) + s =
        Nat.log2 (((closedSet a s b r).image projAB).card) := by
    rw [← h, heq]
  have hs0 : s = 0 := Nat.add_eq_left.mp hEq
  exact (Nat.pos_iff_ne_zero.mp hs) hs0

/-- The existing B3 rate theorem applies to every local recognition context. -/
theorem clockRateBundle {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa) :
    ClockRateBundle kappa :=
  clockRateBundle_of_rindler H.rindler

/--
The boost return period attached to a local-horizon context is the least
positive deficit-free period. This imports no KMS or entropy premise.
-/
theorem euclideanPeriod_isLeast_for_context {a s b r : ℕ} {kappa : ℝ}
    (H : LocalHorizonContext a s b r kappa) :
    IsLeast {T : ℝ | 0 < T ∧ deficitCost (kappa * T) = 0}
      (euclideanPeriod kappa) :=
  euclideanPeriod_isLeast kappa H.rindler.kappa_pos

end LocalRecognitionHorizonCut
end Holography
end IndisputableMonolith
