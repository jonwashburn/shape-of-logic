import Mathlib
import IndisputableMonolith.Ethics.Virtues.FiniteLatticeEnumeration

/-!
# SigmaPreservingIsReachable: Proof in the Abstract Framework

This module addresses the SigmaPreservingIsReachable residual from the
DREAM completeness program in the abstract carrier-and-generator framework
established by `Ethics.Virtues.FiniteLatticeEnumeration`.

## Outcome of the search

The abstract framework admits a *positive* answer when the generator action
is *rich enough*: specifically, when every sigma-preserving function is in
the orbit of the identity under the generator monoid. We make this precise
via the `RichGeneratorAction` predicate.

In the concrete DREAM virtue setting, the question of whether the 14
generators yield a rich action on `List MoralState` reduces to the bond-window
restriction. If yes, no 15th virtue is needed; if no, the smallest
counterexample becomes the 15th generator.

## Honest status

This module proves the *abstract* implication:
  RichGeneratorAction adm act -> SigmaPreservingIsReachable adm act.

The empirical question of whether `RichGeneratorAction` holds for the
concrete DREAM virtue action on `List MoralState` is open and bounded by
the upstream rebuild of `Ethics.MoralState`.

If concrete RichGeneratorAction is later shown to FAIL on a specific
sigma-preserving `f`, the failing `f` is the 15th DREAM virtue generator
and the inductive `DreamVirtue` would need an extra constructor.

## Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Ethics.Virtues.SigmaPreservingProof

open IndisputableMonolith.Ethics.Virtues.FiniteLatticeEnumeration

noncomputable section

/-! ## Rich generator action -/

/-- A generator action is *rich* when every admissibility-preserving function
    can be expressed as the composition of some generator list (on admissible
    inputs). This is the abstract analogue of "the 14 DREAM virtues generate
    every sigma-preserving transformation on List MoralState". -/
def RichGeneratorAction {α G : Type*}
    (adm : Admissible α) (act : GenAction α G) : Prop :=
  ∀ (f : α → α), SigmaPreserving adm f → ReachableTransition adm act f

/-! ## The headline (conditional) theorem -/

/-- Under `RichGeneratorAction`, every sigma-preserving function is reachable.
    This is a near-tautology at the abstract level (RichGeneratorAction *is*
    SigmaPreservingIsReachable in the framework's vocabulary), so the content
    is the *naming*: future investigations of the concrete DREAM action need
    only verify Richness to close the residual. -/
theorem reachable_of_rich
    {α G : Type*} (adm : Admissible α) (act : GenAction α G)
    (h_rich : RichGeneratorAction adm act) :
    SigmaPreservingIsReachable adm act :=
  h_rich

/-! ## Inverse direction: if RichGeneratorAction fails, a 15th virtue exists

The contrapositive: if the abstract framework's `RichGeneratorAction` fails
on `(adm, act)`, there is a sigma-preserving `f` with no generator-list
witness, and this `f` is the canonical "15th generator" needed to extend
the action to a rich one. -/

theorem fifteenth_generator_required_iff_not_rich
    {α G : Type*} (adm : Admissible α) (act : GenAction α G) :
    ¬ RichGeneratorAction adm act ↔
    ∃ (f : α → α), SigmaPreserving adm f ∧ ¬ ReachableTransition adm act f := by
  unfold RichGeneratorAction
  push_neg
  rfl

/-! ## Trivial degenerate case: empty generator action

When the generator type `G` is empty, `RichGeneratorAction` holds iff every
sigma-preserving function equals the identity on admissible inputs. This is
trivially false in general but is a clean boundary case. -/

theorem rich_iff_only_id_on_admissible_for_empty_G
    {α : Type*} (adm : Admissible α)
    (h_inhabited : ∃ x, adm x) :
    RichGeneratorAction adm (act := (fun (g : Empty) => g.elim))
    ↔ ∀ (f : α → α), SigmaPreserving adm f → ∀ x, adm x → f x = x := by
  constructor
  · intro h_rich f h_pres x hadm
    obtain ⟨gs, hgs⟩ := h_rich f h_pres
    cases gs with
    | nil =>
        rw [hgs x hadm]
        unfold composeGenerators
        simp [id]
    | cons g _ =>
        exact g.elim
  · intro h_only_id f h_pres
    refine ⟨[], ?_⟩
    intro x hadm
    have h := h_only_id f h_pres x hadm
    rw [h]
    unfold composeGenerators
    simp [id]

/-! ## Master cert -/

structure SigmaPreservingProofCert
    {α G : Type*} (adm : Admissible α) (act : GenAction α G) where
  abstract_implication : RichGeneratorAction adm act → SigmaPreservingIsReachable adm act
  fifteenth_iff : ¬ RichGeneratorAction adm act ↔
      ∃ (f : α → α), SigmaPreserving adm f ∧ ¬ ReachableTransition adm act f

theorem sigmaPreservingProofCert_holds
    {α G : Type*} (adm : Admissible α) (act : GenAction α G) :
    SigmaPreservingProofCert adm act :=
{ abstract_implication := reachable_of_rich adm act
  fifteenth_iff := fifteenth_generator_required_iff_not_rich adm act }

end

end IndisputableMonolith.Ethics.Virtues.SigmaPreservingProof
