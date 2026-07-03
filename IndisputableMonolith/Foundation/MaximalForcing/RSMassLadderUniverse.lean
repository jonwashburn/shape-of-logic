import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Foundation.PhiForcing

/-!
# Maximal Forcing: the mass-ladder layer (Phase 2 extension, forced scaling)

Fifth concrete instantiation, and the first whose closure genuinely uses two
branches of the trichotomy.

The RS mass law places masses on a phi-ladder: `m(rung) = yardstick · φ^rung`. The
honest separation the execution plan predicted is realized here in machine-checked
form:

* the dimensionless scaling invariant (the ratio of adjacent rungs is `φ`) is
  **forced** over every yardstick, with no gate at all, because it is a structural
  property of the ladder; while
* the absolute yardstick is **independent**: it is a free coordinate, with an
  explicit countermodel pair.

So this universe's closure contains one `Forced` claim and one `Independent`
claim. The classifier exercises both `ClaimClassification.forced` and
`ClaimClassification.independent`, proving the maximal-forcing machinery is not
trivially always-forced: it distinguishes invariants from coordinates.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Foundation.PhiForcing

/-- A point on the phi-ladder: `ladderMass M0 r = M0 · φ^r`. The carrier is the
yardstick `M0`; the rung `r` is the index. -/
noncomputable def ladderMass (M0 : ℝ) (r : ℕ) : ℝ := M0 * φ ^ r

/-- The only class needed: every candidate yardstick. The scaling invariant is
forced here without any tightening. -/
def Lmass0 : AdmissibilityClass ℝ where
  admissible := Set.univ
  label := "every candidate yardstick"

/-- Forced claim: adjacent rungs differ by the factor `φ`. This is the
dimensionless scaling invariant, independent of the yardstick. -/
def isLadderRatioClaim : RealityClaim ℝ where
  label := "ladderMass M0 (r+1) = φ · ladderMass M0 r for all r"
  holds := fun M0 => ∀ r : ℕ, ladderMass M0 (r + 1) = φ * ladderMass M0 r

/-- Independent claim: the yardstick equals one (an absolute-unit choice). -/
def isYardstickClaim : RealityClaim ℝ where
  label := "M0 = 1"
  holds := fun M0 => M0 = 1

/-- The mass-ladder claim universe, carrying one forced and one independent claim. -/
def massUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := Lmass0
  claims := { isLadderRatioClaim, isYardstickClaim }

/-- **The phi-ladder scaling invariant is forced over every yardstick.** No gate
is required: the recurrence is a structural identity of the ladder. -/
theorem forced_ladderRatio : Forced Lmass0.admissible isLadderRatioClaim := by
  intro M0 _ r
  show ladderMass M0 (r + 1) = φ * ladderMass M0 r
  unfold ladderMass
  rw [pow_succ]
  ring

/-- **The yardstick is independent.** Two admissible yardsticks (1 and 2) disagree
on the claim `M0 = 1`. The absolute mass scale is a free coordinate, not a forced
invariant. -/
def yardstickIndepWitness : IndependenceWitness massUniverse isYardstickClaim where
  yes_model := (1 : ℝ)
  no_model := (2 : ℝ)
  yes_admissible := trivial
  no_admissible := trivial
  yes_holds := rfl
  no_fails := by
    intro h
    have h1 : (2 : ℝ) = 1 := h
    norm_num at h1

/-- The yardstick claim is independent (Prop-level), via the witness. -/
theorem yardstick_independent : Independent Lmass0.admissible isYardstickClaim :=
  independent_of_witness yardstickIndepWitness

/-- **Mixed classifier.** Every claim in the mass-ladder closure is classified:
the scaling invariant as `forced`, the yardstick as `independent`. This is the
first universe whose certificate uses both branches. -/
theorem massUniverse_classifier :
    ∀ C : RealityClaim massUniverse.Realization,
      InClosure Primitive.lawOfLogic massUniverse C → ClaimClassification massUniverse C := by
  intro C hC
  have hmem : C ∈ massUniverse.claims := hC
  simp only [massUniverse, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · subst h; exact ClaimClassification.forced forced_ladderRatio
  · subst h; exact ClaimClassification.independent yardstickIndepWitness

/-- A real `MaximalClosureCert` for the mass-ladder universe (mixed
classification). -/
def massUniverseCert : MaximalClosureCert Primitive.lawOfLogic massUniverse where
  classifies := massUniverse_classifier

/-- **Crown trichotomy on the mass-ladder universe.** Every closure claim is
`Forced`, `Independent`, or `Selected`. Here the closure splits into one forced
invariant and one independent coordinate, with `Selected` empty. -/
theorem massUniverse_trichotomy
    (C : RealityClaim massUniverse.Realization)
    (hC : InClosure Primitive.lawOfLogic massUniverse C) :
    Forced Lmass0.admissible C ∨ Independent Lmass0.admissible C ∨ Selected Lmass0.admissible C :=
  maximal_forcing_closure_trichotomy massUniverseCert C hC

/-- The honest mass-layer summary: the scaling invariant is forced, the yardstick
is independent. Dimensionless structure is forced; absolute units are free. -/
theorem mass_scaling_forced_yardstick_free :
    Forced Lmass0.admissible isLadderRatioClaim ∧
    Independent Lmass0.admissible isYardstickClaim :=
  ⟨forced_ladderRatio, yardstick_independent⟩

end MaximalForcing
end Foundation
end IndisputableMonolith
