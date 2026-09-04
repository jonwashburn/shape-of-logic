import Mathlib
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.RequirementFromLedgerClosure
import IndisputableMonolith.Foundation.KernelClosure.CutsetRowA2JoinCost

/-!
# The two remaining words are one word

## What was left

After Arcs 11 to 13 the kernel purchase ledger carried two sentences that were
not theorems of the floor facts:

* row 4 (hierarchy): "a level's join is a recognition", under which the parts of
  a join are distinct (`CutsetRowA2JoinCost.costly_iff_distinct`);
* row 5 (space): "a completed recognition remains distinguishable from its
  reversal by something the substrate can post"
  (`RequirementFromLedgerClosure.PersistedPostedDistinction`), under which
  `D = 3`.

This module shows they are the same sentence, said of two objects, and says
exactly what separates the row that closed from the row that did not.

## The one sentence

The deformation-erasure principle (`LinkingNecessity.DeformationErasurePrinciple`,
DEP) is stated for any `PairKinematics`: a configuration space with a
recognition-free deformation relation, a *balanced* configuration `split` where
the act is erased, and the *realized* configuration `pair`. DEP says a
deformation-invariant integer reading, zero on the balanced configuration, is
nonzero on the realized one: **recognition-free deformation cannot carry a
completed recognition to its balanced configuration.**

* The join is such a kinematics (`joinKinematics`): configurations are join
  ratios, the balanced configuration is ratio `1` (where `J 1 = 0`), the
  realized one is the join ratio. A ratio has no recognition-free deformation:
  changing it costs `J` (T5), so `deform` is equality. DEP for the join is
  exactly "the parts are distinct" (`hierarchy_word_iff_dep`).
* Persistence is DEP for the spatial pair kinematics, in both directions
  (`persistence_iff_dep`): the `LedgerReading` of `RequirementFromLedgerClosure`
  and the `PairingObservable` of `LinkingNecessity` are the same object once
  invariance is discharged from the cost layer.

## What separates the two rows

`dep_rigid_iff`: in a **rigid** kinematics, one where every deformation is
equality (no configuration changes without a post), DEP is bare distinctness of
the realized configuration from the balanced one. That is the join, and it is
also the discrete tower, where every unit step posts a bit
(`CutsetRow5Tower.floorReader_moves`); in a rigid kinematics DEP holds whenever
`pair ≠ split` and constrains nothing further (`rigid_dep_of_ne`). The row 4
word closed because its kinematics is rigid and its distinctness is a theorem
of cost (`J 1 = 0`, `J x > 0` off `1`).

The row 5 word does not close by the same route because its kinematics is not
rigid: `D = 3` is forced only through `SpatialDualPairRealization`, whose
deformation relation is continuous isotopy, a motion that posts nothing. There
DEP is stability, not distinctness, and bare distinctness of configurations does
not give it (`config_distinctness_does_not_force_dep`); a complete realization
refutes it (`dep_not_forced_by_realization_layer`). So the whole of what the
kernel does not derive is one sentence, and it is about the realization layer
in which traces can move without posting: **a completed recognition cannot be
carried to its balanced configuration by a motion that posts nothing.** In a
world with no free motion (the tower alone) the sentence is trivially true and
selects no dimension; in a world with free motion it is the theory's account of
space and selects three.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace OneWord

open LinkingNecessity RequirementFromLedgerClosure RowA2JoinCost
open ClosedFramework LadderCensus Row4Ladder RowA2Join

/-! ## Rigid kinematics: DEP is distinctness -/

/-- A kinematics is rigid when every recognition-free deformation is equality:
no configuration changes without a post. -/
def Rigid (X : PairKinematics) : Prop := ∀ a b, X.deform a b → a = b

/-- **In a rigid kinematics DEP is bare distinctness** of the realized
configuration from the balanced one. -/
theorem dep_rigid_iff (X : PairKinematics) (hX : Rigid X) :
    DeformationErasurePrinciple X ↔ X.pair ≠ X.split := by
  constructor
  · intro h heq
    apply dep_separates_pair_from_split X h
    rw [heq]
    exact X.deform_refl _
  · intro hne
    classical
    refine ⟨⟨fun c => if c = X.pair then 1 else 0, ?_, ?_⟩, ?_⟩
    · intro a b hab
      rw [hX a b hab]
    · simp [hne.symm]
    · simp

/-- In a rigid kinematics DEP holds as soon as the two configurations differ,
whatever else is true: rigidity selects nothing. -/
theorem rigid_dep_of_ne (X : PairKinematics) (hX : Rigid X) (hne : X.pair ≠ X.split) :
    DeformationErasurePrinciple X :=
  (dep_rigid_iff X hX).mpr hne

/-! ## The join as a kinematics -/

/-- **The join kinematics.** Configurations are join ratios; the balanced
configuration is ratio `1` (`J 1 = 0`); the realized configuration is the join
ratio of the levels. A ratio has no recognition-free deformation (changing a
ratio costs `J`, T5), so `deform` is equality. -/
@[reducible] noncomputable def joinKinematics (s : ℕ → ℝ) (a b n : ℕ) : PairKinematics where
  Config := ℝ
  deform := Eq
  deform_refl := fun _ => rfl
  deform_symm := Eq.symm
  deform_trans := Eq.trans
  split := 1
  pair := joinRatio s a b n

theorem joinKinematics_rigid (s : ℕ → ℝ) (a b n : ℕ) : Rigid (joinKinematics s a b n) :=
  fun _ _ h => h

/-- The balanced configuration of the join is the cost-free one. -/
theorem join_split_costs_nothing (s : ℕ → ℝ) (a b n : ℕ) :
    Cost.Jcost (joinKinematics s a b n).split = 0 :=
  (Cost.Jcost_eq_zero_iff 1 one_pos).mpr rfl

/-- **The hierarchy word is DEP.** Under similarity, DEP for the join kinematics
of two levels `a ≤ b` is exactly "the parts are distinct", `a < b`. -/
theorem hierarchy_word_iff_dep {F : ClosedObservableFramework} {ρ : ℝ}
    (hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b n : ℕ) (hab : a ≤ b)
    (hj : TwoPartJoin (orbitLevels' F base) a b) :
    DeformationErasurePrinciple (joinKinematics (orbitLevels' F base) a b n) ↔ a < b := by
  rw [dep_rigid_iff _ (joinKinematics_rigid _ a b n),
    ← costly_iff_distinct hρ base a b n hab hj]
  show joinRatio (orbitLevels' F base) a b n ≠ 1 ↔ 0 < joinCost (orbitLevels' F base) a b n
  unfold joinCost
  have hpos : 0 < joinRatio (orbitLevels' F base) a b n := by
    unfold joinRatio
    exact div_pos (orbitLevels_pos F base _) (orbitLevels_pos F base _)
  constructor
  · intro hne
    exact Cost.Jcost_pos_of_ne_one _ hpos hne
  · intro hc heq
    rw [heq, (Cost.Jcost_eq_zero_iff 1 one_pos).mpr rfl] at hc
    exact lt_irrefl 0 hc

/-! ## Persistence is DEP -/

/-- **Persistence and DEP are the same sentence.** A ledger reading is a pairing
observable once invariance is discharged from the cost layer, and a pairing
observable is a ledger reading with zero cost (the no-refund clause is then
vacuous, since invariance makes its hypothesis false). -/
theorem persistence_iff_dep (X : PairKinematics) :
    PersistedPostedDistinction X ↔ DeformationErasurePrinciple X := by
  constructor
  · exact persisted_gives_dep X
  · rintro ⟨P, hP⟩
    refine ⟨⟨P.pairing, fun _ _ => 0, fun _ _ _ => rfl, ?_, P.split_zero⟩, hP⟩
    intro a b hab hne
    exact absurd (P.deform_invariant a b hab) hne

/-! ## Certificate -/

/-- The one-word certificate. -/
structure Cert : Prop where
  /-- In a rigid kinematics DEP is bare distinctness. -/
  rigid_dep : ∀ X : PairKinematics, Rigid X →
    (DeformationErasurePrinciple X ↔ X.pair ≠ X.split)
  /-- The join kinematics is rigid. -/
  join_rigid : ∀ (s : ℕ → ℝ) (a b n : ℕ), Rigid (joinKinematics s a b n)
  /-- Its balanced configuration is the cost-free ratio `1`. -/
  join_balanced_free : ∀ (s : ℕ → ℝ) (a b n : ℕ),
    Cost.Jcost (joinKinematics s a b n).split = 0
  /-- The hierarchy word is DEP for the join. -/
  hierarchy_is_dep : ∀ {F : ClosedObservableFramework} {ρ : ℝ}
    (_hρ : ∀ s, F.r (F.T s) = ρ * F.r s) (base : F.S) (a b n : ℕ), a ≤ b →
    TwoPartJoin (orbitLevels' F base) a b →
    (DeformationErasurePrinciple (joinKinematics (orbitLevels' F base) a b n) ↔ a < b)
  /-- The space word (persistence) is DEP for the pair. -/
  space_is_dep : ∀ X : PairKinematics,
    PersistedPostedDistinction X ↔ DeformationErasurePrinciple X
  /-- In the non-rigid case distinctness does not give DEP. -/
  distinctness_not_enough : ∃ X : PairKinematics,
    X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X
  /-- DEP is a genuine input of the realization layer. -/
  genuine_input : ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
    ¬ DeformationErasurePrinciple R.kin
  /-- DEP forces `D = 3` in every spatial realization. -/
  forces_three : ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
    DeformationErasurePrinciple R.kin → D = 3
  /-- The ground: nothing cannot recognize itself. -/
  ground_mp : Recognition.MP

theorem cert : Cert where
  rigid_dep := dep_rigid_iff
  join_rigid := joinKinematics_rigid
  join_balanced_free := join_split_costs_nothing
  hierarchy_is_dep := fun hρ base a b n hab hj => hierarchy_word_iff_dep hρ base a b n hab hj
  space_is_dep := persistence_iff_dep
  distinctness_not_enough := config_distinctness_does_not_force_dep
  genuine_input := dep_not_forced_by_realization_layer
  forces_three := dep_forces_D3
  ground_mp := Recognition.mp_holds

end OneWord
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
