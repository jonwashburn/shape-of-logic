import IndisputableMonolith.Mathematics.HodgeClassicalStatement
import IndisputableMonolith.Mathematics.HodgeDeltaBridge.StatementVacuityWitness

/-!
# δ-Hodge Bridge: the statement trilemma (RED-FLAG GUARD, sharpened)

This module sharpens `StatementVacuityWitness` from a single vacuity result
into a two-sided bracket that pins down *why* no quick fix to the statement
interface works. Read it before claiming any Hodge progress.

## The trilemma

A would-be Hodge statement has the shape "every rational `(p,p)` class is the
cycle class of an algebraic cycle." Everything turns on where the cycle-class
map `cl : AlgebraicCycle X p → H^{2p}(X,ℚ)` comes from. There are exactly three
ways to source it, and two of them are degenerate:

1. **Prover-chosen map** (the base statement
   `HodgeClassicalStatement.RationalHodgeConjectureStatement`). The prover
   supplies `cl`, including its own target module. Picking the zero module
   `PUnit` discharges the whole thing. **VACUOUS** — Lean-proven in
   `StatementVacuityWitness.rational_hodge_statement_is_vacuous`, re-exported
   here as `horn_prover_chosen_is_vacuous`.

2. **Adversary-chosen map** (fix the map externally as *arbitrary* data:
   `ExternalArbitraryMapStatement`). Now the cohomology is a genuine nonzero
   ℚ-module, but the map is still free data, so the adversary picks the zero
   map and a nonzero target class that the zero map cannot hit. **FALSE** —
   Lean-proven below in `external_arbitrary_map_statement_false`.

3. **Genuine geometric map** (the only correct option). `cl` is *the* canonical
   cycle class map of algebraic geometry: it is determined by the geometry of
   `X`, not chosen by either party. This is neither vacuous nor false; it is the
   real Hodge conjecture. It cannot be written down on the current substrate
   because `SmoothProjectiveComplexVariety`, `RationalCohomologyClass`, and
   `AlgebraicCycle` are interface stubs with no scheme structure, no genuine
   `H^{2p}(X,ℚ)`, and no genuine cycle class map.

`statement_trilemma_extremes` packages horns 1 and 2 as a single theorem: the
prover-chosen statement is *provable* and the adversary-chosen statement is
*refutable*. A statement that is simultaneously provable-when-loosened and
refutable-when-tightened is carrying none of its intended mathematical content
at the seam where the geometry should live.

## Where the in-between statement (`FullTargetRationalHodgeStatement`) sits

`HodgeDeltaBridge.FullTargetRationalHodgeStatement` fixes the cohomology
externally (blocking horn 1's zero-module trick) but still lets the prover pick
`cycleClass` out of the hollow `AlgebraicCycle` type. Its status is genuinely
subtle and *cardinality-dependent*: when `X.carrier` is small (e.g. a one-point
stub) and the external cohomology is large, the additivity axioms
(`map_add` over the `⊕`-cycle-addition, `map_smul` over coefficient scaling)
restrict the reachable image, so it can fail to be vacuous; when the prover is
allowed bespoke cycles per class it can be discharged. That a "statement" flips
between vacuous and false depending on the *cardinality of an interface stub* is
itself the proof that it is not referee-grade. We do not pin its exact status
here; the two clean extremes above already establish the trilemma.

## The only correct path (named, not hand-waved)

A genuine statement needs three Mathlib-native objects that do not exist yet:

* `H^{2p}(X,ℚ)` as real singular/de Rham cohomology with its Hodge
  decomposition — REQUIRES Mathlib complex/Kähler Hodge theory (absent).
* the canonical cycle class map `CH^p(X) → H^{2p}(X,ℚ)` — REQUIRES Mathlib
  Chow groups / intersection theory for smooth projective varieties (absent).
* `AlgebraicCycle` carrying real closed algebraic subvariety data — REQUIRES
  the scheme/variety structure on `X.carrier` (absent; `carrier` is a bare
  `Type u` with a topology).

## Honest status of the mathematics itself (independent of formalization)

Even with those objects in hand, the conjecture is open. The proven sub-cases
are: `p = 0` and `p = n` (trivial), `p = 1` (the Lefschetz `(1,1)` theorem, via
the exponential sequence), and `p = n-1` (hard Lefschetz duality from `p = 1`).
The general case is open. The *integral* version is known **false** by
Atiyah–Hirzebruch (Steenrod-operation / spectral-sequence obstructions), so any
route that claims "the minimal-cost current representative is automatically
integral" is refuted by those examples. A Recognition Science route must
therefore engage the Atiyah–Hirzebruch obstruction directly; the rational
version asks only that some integer multiple of the class be algebraic, which
the integral counterexamples do not settle.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDeltaBridge
namespace StatementTrilemma

open HodgeClassicalStatement

universe u

/-- Horn 1, re-exported: the prover-chosen-map statement is vacuous. -/
theorem horn_prover_chosen_is_vacuous : RationalHodgeConjectureStatement.{u} :=
  VacuityWitness.rational_hodge_statement_is_vacuous

/-- A genuine **nonzero** rational cohomology object over `X`, living in
`Type u`, with carrier `ULift ℚ`. Unlike the zero-module stub used to discharge
horn 1, this carrier has two distinct elements, so it cannot be collapsed by a
`Subsingleton` argument. -/
def rationalLineCohomology (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) :
    RationalCohomologyClass.{u} X where
  degree := 2 * p
  carrier := ULift.{u} ℚ
  zero := ⟨0⟩
  add := fun a b => ⟨a.down + b.down⟩
  neg := fun a => ⟨-a.down⟩
  smul := fun q a => ⟨q * a.down⟩
  add_assoc := by
    intro a b c; apply ULift.ext
    show (a.down + b.down) + c.down = a.down + (b.down + c.down); ring
  add_comm := by
    intro a b; apply ULift.ext
    show a.down + b.down = b.down + a.down; ring
  add_zero := by
    intro a; apply ULift.ext
    show a.down + (0 : ℚ) = a.down; ring
  add_neg := by
    intro a; apply ULift.ext
    show a.down + (-a.down) = (0 : ℚ); ring
  smul_one := by
    intro a; apply ULift.ext
    show (1 : ℚ) * a.down = a.down; ring
  smul_zero := by
    intro q; apply ULift.ext
    show q * (0 : ℚ) = (0 : ℚ); ring
  smul_add := by
    intro q a b; apply ULift.ext
    show q * (a.down + b.down) = q * a.down + q * b.down; ring
  mul_smul := by
    intro r s a; apply ULift.ext
    show (r * s) * a.down = r * (s * a.down); ring
  add_smul := by
    intro r s a; apply ULift.ext
    show (r + s) * a.down = r * a.down + s * a.down; ring
  zero_smul := by
    intro a; apply ULift.ext
    show (0 : ℚ) * a.down = (0 : ℚ); ring
  rationalLattice := ULift.{u} ℚ
  rationalCoordinates := id

/-- Horn 2 data: a fixed, **externally supplied** cohomology and cycle-class map,
together with a single target class. "Externally supplied" means the cycle-class
map is free data of the problem rather than the canonical geometric map; that is
exactly the freedom an adversary exploits. -/
structure ExternalCycleClassData
    (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) where
  cohomology : RationalCohomologyClass.{u} X
  degree_eq : cohomology.degree = 2 * p
  cycleClass : AlgebraicCycle.{u, u} X p → cohomology.carrier
  target : cohomology.carrier

/-- Horn 2 statement: with the cycle-class map fixed externally as arbitrary
data, every supplied target class is realized by some cycle. -/
def ExternalArbitraryMapStatement
    (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) : Prop :=
  ∀ D : ExternalCycleClassData.{u} X p,
    ∃ Z : AlgebraicCycle.{u, u} X p, D.cycleClass Z = D.target

/-- **Horn 2 is false.** Fixing the cycle-class map externally as arbitrary data
lets the adversary take the zero map into a genuine nonzero cohomology and pick a
nonzero target the zero map can never hit. No construction of `X` is needed: the
refutation holds for *every* smooth projective complex variety. -/
theorem external_arbitrary_map_statement_false
    (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ) :
    ¬ ExternalArbitraryMapStatement.{u} X p := by
  intro H
  obtain ⟨_Z, hZ⟩ := H
    { cohomology := rationalLineCohomology X p
      degree_eq := rfl
      cycleClass := fun _ => (⟨0⟩ : ULift.{u} ℚ)
      target := (⟨1⟩ : ULift.{u} ℚ) }
  have hcontra : (0 : ℚ) = (1 : ℚ) := congrArg ULift.down hZ
  exact absurd hcontra (by norm_num)

/-- **The trilemma, as one theorem.** The prover-chosen-map statement is
*provable* (horn 1, vacuous) and, simultaneously, the adversary-chosen-map
statement is *refutable* (horn 2, false). A statement bracketed this way carries
none of its intended geometric content; only the genuine cycle class map
(unavailable on the current substrate) gives the real, non-degenerate Hodge
conjecture. -/
theorem statement_trilemma_extremes :
    RationalHodgeConjectureStatement.{u}
      ∧ (∀ (X : SmoothProjectiveComplexVariety.{u}) (p : ℕ),
            ¬ ExternalArbitraryMapStatement.{u} X p) :=
  ⟨horn_prover_chosen_is_vacuous, external_arbitrary_map_statement_false⟩

end StatementTrilemma
end HodgeDeltaBridge
end Mathematics
end IndisputableMonolith
