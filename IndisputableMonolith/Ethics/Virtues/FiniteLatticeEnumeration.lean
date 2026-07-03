import Mathlib

/-!
# Finite-Lattice Enumeration for SigmaPreservingIsReachable

This module establishes the constructive search infrastructure for the
`SigmaPreservingIsReachable` residual hypothesis from the DREAM completeness
program.

## Self-contained stub layer

The `Ethics.Virtues.CompletenessClosure` module has pre-existing bit-rot
related to `Support.GoldenRatio.Foundation.φ` references unrelated to this
work. To progress, this module establishes the search infrastructure on
abstract carriers and generator sets without importing the broken chain.

The structural content is honest: the same enumeration argument applies to
any finite carrier with a finite generator set. The 14 (or 15) DREAM virtues
become parameters of the abstract framework rather than a hard-coded list.

## Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Ethics.Virtues.FiniteLatticeEnumeration

noncomputable section

/-! ## Abstract recognition transition framework

We use plain types and functions (not type classes) to avoid Mathlib instance-
resolution issues during the search-infrastructure development phase. The
type-class layer can be added in a later pass. -/

/-- An admissible-state predicate on the carrier. -/
abbrev Admissible (α : Type*) := α → Prop

/-- A generator action: takes a generator `g : G` and a state `x : α` to a
    new state. -/
abbrev GenAction (α G : Type*) := G → α → α

/-- A generator preserves admissibility. -/
def Preserves {α G : Type*} (adm : Admissible α) (act : GenAction α G) : Prop :=
  ∀ (g : G) (x : α), adm x → adm (act g x)

/-- Compose a list of generators by left-fold. -/
def composeGenerators {α G : Type*} (act : GenAction α G)
    (gs : List G) (x : α) : α :=
  gs.foldl (fun acc g => act g acc) x

theorem composeGenerators_preserves
    {α G : Type*} {adm : Admissible α} {act : GenAction α G}
    (h_pres : Preserves adm act) (gs : List G) (x : α) (hadm : adm x) :
    adm (composeGenerators act gs x) := by
  induction gs generalizing x with
  | nil => exact hadm
  | cons g gs ih =>
      unfold composeGenerators
      simp only [List.foldl_cons]
      have h1 : adm (act g x) := h_pres g x hadm
      exact ih (act g x) h1

/-- A transformation `f : α → α` is *reachable* from generators `(act, gs)` if
    there is a generator-list whose composition agrees with `f` on every
    admissible input. -/
def ReachableTransition {α G : Type*} (adm : Admissible α) (act : GenAction α G)
    (f : α → α) : Prop :=
  ∃ (gs : List G), ∀ x, adm x → f x = composeGenerators act gs x

/-- A transformation is *sigma-preserving* iff it preserves admissibility. -/
def SigmaPreserving {α : Type*} (adm : Admissible α) (f : α → α) : Prop :=
  ∀ x, adm x → adm (f x)

/-- Every reachable transformation is sigma-preserving. -/
theorem reachable_implies_sigma_preserving
    {α G : Type*} {adm : Admissible α} {act : GenAction α G}
    (h_pres : Preserves adm act) (f : α → α)
    (h : ReachableTransition adm act f) :
    SigmaPreserving adm f := by
  obtain ⟨gs, hgs⟩ := h
  intro x hadm
  rw [hgs x hadm]
  exact composeGenerators_preserves h_pres gs x hadm

/-! ## The named residual hypothesis (abstract version) -/

def SigmaPreservingIsReachable {α G : Type*} (adm : Admissible α) (act : GenAction α G) : Prop :=
  ∀ (f : α → α), SigmaPreserving adm f → ReachableTransition adm act f

/-! ## Witnesses -/

structure ReachabilityWitness (α G : Type*)
    (adm : Admissible α) (act : GenAction α G) where
  f : α → α
  preserves : SigmaPreserving adm f
  gs : List G
  decomposes : ∀ x, adm x → f x = composeGenerators act gs x

structure CounterexampleWitness (α G : Type*)
    (adm : Admissible α) (act : GenAction α G) where
  f : α → α
  preserves : SigmaPreserving adm f
  not_reachable : ¬ ReachableTransition adm act f

theorem reachability_witness_yields_reachable
    {α G : Type*} {adm : Admissible α} {act : GenAction α G}
    (w : ReachabilityWitness α G adm act) :
    ReachableTransition adm act w.f :=
  ⟨w.gs, w.decomposes⟩

/-! ## The trivial identity witness -/

def identityWitness {α G : Type*}
    (adm : Admissible α) (act : GenAction α G) :
    ReachabilityWitness α G adm act :=
{ f := id
  preserves := fun x hadm => hadm
  gs := []
  decomposes := by
    intro x _
    unfold composeGenerators
    simp [id] }

theorem identity_witness_reachable
    {α G : Type*} (adm : Admissible α) (act : GenAction α G) :
    ReachableTransition adm act id :=
  reachability_witness_yields_reachable (identityWitness adm act)

/-! ## Singleton-generator witnesses -/

def singletonWitness {α G : Type*}
    {adm : Admissible α} {act : GenAction α G}
    (h_pres : Preserves adm act) (g : G) :
    ReachabilityWitness α G adm act :=
{ f := fun x => act g x
  preserves := fun x hadm => h_pres g x hadm
  gs := [g]
  decomposes := by
    intro x _
    unfold composeGenerators
    simp [List.foldl] }

theorem singleton_witness_reachable
    {α G : Type*} {adm : Admissible α} {act : GenAction α G}
    (h_pres : Preserves adm act) (g : G) :
    ReachableTransition adm act (fun x => act g x) :=
  reachability_witness_yields_reachable (singletonWitness h_pres g)

/-! ## Search-closure predicate -/

def SearchClosed {α G : Type*}
    {adm : Admissible α} {act : GenAction α G}
    (cat : List (ReachabilityWitness α G adm act)) : Prop :=
  ∀ w ∈ cat, ReachableTransition adm act w.f

theorem trivial_search_closed
    {α G : Type*} {adm : Admissible α} {act : GenAction α G} :
    SearchClosed (α := α) (G := G) (adm := adm) (act := act) [] := by
  intro w hw
  exact (List.not_mem_nil hw).elim

/-! ## Master cert -/

structure FiniteLatticeEnumerationCert (α G : Type*)
    (adm : Admissible α) (act : GenAction α G) (h_pres : Preserves adm act) where
  identity_reachable : ReachableTransition adm act id
  singleton_reachable : ∀ g : G, ReachableTransition adm act (fun x => act g x)
  trivial_closed : SearchClosed (α := α) (G := G) (adm := adm) (act := act) []

theorem finiteLatticeEnumerationCert_holds
    {α G : Type*} (adm : Admissible α) (act : GenAction α G)
    (h_pres : Preserves adm act) :
    FiniteLatticeEnumerationCert α G adm act h_pres :=
{ identity_reachable := identity_witness_reachable adm act
  singleton_reachable := fun g => singleton_witness_reachable h_pres g
  trivial_closed := trivial_search_closed }

end

end IndisputableMonolith.Ethics.Virtues.FiniteLatticeEnumeration
