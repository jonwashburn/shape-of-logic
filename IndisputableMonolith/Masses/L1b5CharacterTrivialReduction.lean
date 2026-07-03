import Mathlib
import IndisputableMonolith.Masses.L1b4ChannelSchemaNonvacuity

/-!
# L1b5 Character-Triviality Reduction (Track B, D5)

This module discharges the panel-re-localized Track-B target after the first
`ledger-positivity -> trivial-representation` prose argument was REJECTED by the
anti-circularity gate (2026-07-01). The rejection's decisive content was the
`Z2` sign-character counter-model `K_chi(x,y) = 48⁻¹ χ(x) χ(y)`: it showed that
naming "classical positivity forces the trivial representation" without a
lake-checked bridge is circular, and that the true remaining physical content is
a single sign fact about the flip generator of the boundary ledger.

## What is proved here (all THEOREM, axiom-clean modulo the finite `Q3Flag`
## `Fintype`/`Decidable` machinery)

Working in the locked operator class (character projectors of B3 sign
characters, `L1b4`), the whole of conjuncts (i)-(iii) is free, so admissibility
of `signKernel eps` collapses to a statement about the character `eps` itself:

* `signChar_signKernel_b3Invariant`   -- (i) for any B3 sign character;
* `uniformReynolds_b3Invariant`       -- (i) for the uniform projector `R`;
* `uniformReynolds_admissible`        -- `R` is admissible;
* `admissible_iff_trivial_character`  -- **the D5 reduction**:
    `AdmissibleChannelKernel (signKernel eps) ↔ (∀ i j, eps i = eps j)`,
    i.e. the channel is admissible iff its boundary sign character is *trivial*
    (constant), with no positivity axiom assumed on the ledger;
* `admissible_iff_uniformReynolds`    -- the same, phrased as `= R`;
* `tauOdd_flip_not_admissible`        -- **the flip-twist obstruction**: if the
    character sign-flips under the flip generator (`tauOdd q3Tau`), the channel
    is not admissible;
* `boundary_sector_dichotomy`         -- on the two boundary competitors
    `{trivial, flip-parity}`: the untwisted one (trivial) is admissible and the
    twisted one (flip-parity) is not.

## Consequence: L1b reduces to one physical fact

`admissible_iff_trivial_character` is the honest reduction the panel demanded:
**L1b (physical admissibility of the charged channel) is equivalent to the
charged boundary sign character being trivial.** The sole remaining physical
input is that the charged ledger's posting-composition rule does not pick up a
sign, i.e. its boundary character is constant. This is stated, not assumed:
`charged_channel_admissible_of_trivial_character` is the conditional closure
keyed to that one fact, and it introduces NO positivity axiom on the ledger.

## Honest boundary and the sharpened frontier

The converse "untwisted under the single flip generator `q3Tau` implies
admissible" is FALSE over the full B3 character group (e.g. the
permutation-sign character is `q3Tau`-untwisted yet mixed-sign), so it is NOT
claimed here. The correct criterion is triviality of the character (constant
sign), for which tau-oddness under the flip generator is a *sufficient
obstruction* and, within the boundary sign sector `{trivial, flip-parity}`, the
exact discriminator. Whether the physical charged character lives in that
sign-bit sector is the remaining physical-modeling fact (Track-B D3), and it is
left OPEN. L1b and L1 remain OPEN.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1b5CharacterTrivialReduction

open L1b1UniformReynoldsEngine
open L1b2SignKernelExclusion
open L1b3Q3FlagCarrier
open L1bChargedChannelAdmissible

noncomputable section

local instance : Nonempty Q3Flag := ⟨b3Id⟩

/--
A B3 sign character on the principal carrier: sign-valued (`±1`) and
multiplicative under the principal action. This packages exactly the two facts
that make conjuncts (i)-(iii) free for the projector `signKernel eps`.
-/
structure B3SignCharacter (eps : Q3Flag → ℝ) : Prop where
  sign : signValues eps
  mul  : ∀ g x, eps (b3Act g x) = eps g * eps x

/-- The trivial (constant-one) character is a B3 sign character. -/
theorem ones_b3SignCharacter : B3SignCharacter (ones Q3Flag) := by
  refine ⟨?_, ?_⟩
  · intro i; exact Or.inl rfl
  · intro g x; simp [ones]

/-- The flip-parity character is a B3 sign character. -/
theorem flipParityChar_b3SignCharacter : B3SignCharacter flipParityChar :=
  ⟨flipParityChar_signValues, fun g x => flipParityChar_mul g x⟩

/--
Any B3 sign character projector is B3-invariant (conjunct (i)).

This generalizes `flipParitySignKernel_b3Invariant`:
`K(g·x, g·y) = c⁻¹ χ(g·x) χ(g·y) = c⁻¹ χ(g)² χ(x) χ(y) = c⁻¹ χ(x) χ(y) = K(x,y)`.
-/
theorem signChar_signKernel_b3Invariant {eps : Q3Flag → ℝ}
    (hchar : B3SignCharacter eps) :
    b3Invariant (signKernel eps) := by
  intro g x y
  have hx : eps (b3Act g x) = eps g * eps x := hchar.mul g x
  have hy : eps (b3Act g y) = eps g * eps y := hchar.mul g y
  have hg2 : eps g * eps g = 1 := sign_mul_self hchar.sign g
  rw [signKernel_apply hchar.sign (b3Act g x) (b3Act g y),
      signKernel_apply hchar.sign x y, hx, hy]
  linear_combination
    ((Fintype.card Q3Flag : ℝ)⁻¹ * eps x * eps y) * hg2

/-- The uniform Reynolds projector is B3-invariant (it is a constant kernel). -/
theorem uniformReynolds_b3Invariant :
    b3Invariant (uniformReynolds Q3Flag) := by
  intro g x y
  rw [uniformReynolds_apply (α := Q3Flag) (b3Act g x) (b3Act g y),
      uniformReynolds_apply (α := Q3Flag) x y]

/-- The uniform Reynolds projector is admissible (all four conjuncts). -/
theorem uniformReynolds_admissible :
    AdmissibleChannelKernel (uniformReynolds Q3Flag) :=
  ⟨uniformReynolds_b3Invariant,
    uniformReynolds_idempotent,
    uniformReynolds_diagonalContent_one,
    uniformReynolds_entrywiseNonneg⟩

/--
A sign character whose values are all equal (the trivial character) collapses to
the uniform Reynolds projector. This is the "trivial-representation = `R`"
identification, proved from the character being constant, with no positivity
axiom.
-/
theorem signKernel_eq_uniformReynolds_of_all_signs_equal {eps : Q3Flag → ℝ}
    (hε : signValues eps) (heq : ∀ i j, eps i = eps j) :
    signKernel eps = uniformReynolds Q3Flag := by
  ext i j
  rw [signKernel_apply hε i j, uniformReynolds_apply (α := Q3Flag) i j]
  have hs : eps i * eps j = 1 := by
    rw [← heq i j]; exact sign_mul_self hε i
  rw [mul_assoc, hs, mul_one]

/--
**The D5 reduction.** For a B3 sign character `eps`, its projector is admissible
iff the character is trivial (all signs equal). No positivity axiom on the
ledger is assumed; conjuncts (i)-(iii) are supplied structurally and conjunct
(iv) is shown equivalent to triviality of the character.
-/
theorem admissible_iff_trivial_character {eps : Q3Flag → ℝ}
    (hchar : B3SignCharacter eps) :
    AdmissibleChannelKernel (signKernel eps) ↔ (∀ i j, eps i = eps j) := by
  constructor
  · rintro ⟨_, _, _, hnn⟩
    exact signKernel_entrywiseNonneg_forces_all_signs_equal hchar.sign hnn
  · intro heq
    have hR : signKernel eps = uniformReynolds Q3Flag :=
      signKernel_eq_uniformReynolds_of_all_signs_equal hchar.sign heq
    rw [hR]; exact uniformReynolds_admissible

/-- The D5 reduction, phrased as pinning the kernel to `R`. -/
theorem admissible_iff_uniformReynolds {eps : Q3Flag → ℝ}
    (hchar : B3SignCharacter eps) :
    AdmissibleChannelKernel (signKernel eps)
      ↔ signKernel eps = uniformReynolds Q3Flag := by
  constructor
  · intro h
    exact signKernel_eq_uniformReynolds_of_all_signs_equal hchar.sign
      ((admissible_iff_trivial_character hchar).mp h)
  · intro h; rw [h]; exact uniformReynolds_admissible

/--
**The flip-twist obstruction.** If the sign character picks up a sign under the
flip generator (`tauOdd q3Tau`), then its channel is not admissible. This is the
lake-checked form of the panel's re-localization: a composition rule twisted
under the flip generator cannot yield an admissible (entrywise-nonnegative)
channel.
-/
theorem tauOdd_flip_not_admissible {eps : Q3Flag → ℝ}
    (hε : signValues eps) (hτ : tauOdd q3Tau eps) :
    ¬ AdmissibleChannelKernel (signKernel eps) := by
  intro h
  exact signKernel_not_entrywiseNonneg_of_tauOdd hε hτ h.2.2.2

/-- Even under the flip generator: the character does not change sign. -/
def tauEven (eps : Q3Flag → ℝ) : Prop :=
  ∀ i, eps (q3Tau i) = eps i

/-- The trivial character is untwisted (tau-even) under the flip generator. -/
theorem ones_tauEven : tauEven (ones Q3Flag) := by
  intro i; rfl

/--
**Boundary-sector dichotomy.** On the two boundary sign competitors, the
untwisted one (the trivial character) is admissible and pins the channel to `R`,
while the twisted one (the flip-parity character) is not admissible. So within
`{trivial, flip-parity}`, "untwisted under the flip generator" is exactly
"admissible".
-/
theorem boundary_sector_dichotomy :
    (tauEven (ones Q3Flag)
      ∧ AdmissibleChannelKernel (signKernel (ones Q3Flag))
      ∧ signKernel (ones Q3Flag) = uniformReynolds Q3Flag)
    ∧ (tauOdd q3Tau flipParityChar
      ∧ ¬ AdmissibleChannelKernel (signKernel flipParityChar)) := by
  refine ⟨⟨ones_tauEven, ?_, ?_⟩, flipParityChar_tauOdd, ?_⟩
  · exact (admissible_iff_uniformReynolds ones_b3SignCharacter).mpr rfl
  · rfl
  · exact tauOdd_flip_not_admissible flipParityChar_signValues flipParityChar_tauOdd

/--
**Conditional L1b closure.** If the physical charged boundary sign character is
trivial (constant, i.e. its posting-composition rule picks up no sign), then its
channel is admissible and equals the uniform Reynolds projector `R`.

The sole physical input is triviality of the character. No positivity axiom is
placed on the ledger. This is the honest reduction of L1b to one sign fact;
whether the physical charged character is in fact trivial (equivalently, that it
lives in the boundary sign sector AND is untwisted under the flip generator)
remains OPEN (Track-B D3), and so L1b and L1 remain OPEN.
-/
theorem charged_channel_admissible_of_trivial_character {eps : Q3Flag → ℝ}
    (hchar : B3SignCharacter eps) (htriv : ∀ i j, eps i = eps j) :
    AdmissibleChannelKernel (signKernel eps)
      ∧ signKernel eps = uniformReynolds Q3Flag :=
  ⟨(admissible_iff_trivial_character hchar).mpr htriv,
    signKernel_eq_uniformReynolds_of_all_signs_equal hchar.sign htriv⟩

/-- L1b5 D5 reduction certificate. This is NOT an L1b or L1 closure. -/
structure CharacterTrivialReductionCert where
  invariant_free :
    ∀ {eps : Q3Flag → ℝ}, B3SignCharacter eps → b3Invariant (signKernel eps)
  uniform_admissible :
    AdmissibleChannelKernel (uniformReynolds Q3Flag)
  reduction :
    ∀ {eps : Q3Flag → ℝ}, B3SignCharacter eps →
      (AdmissibleChannelKernel (signKernel eps) ↔ (∀ i j, eps i = eps j))
  flip_twist_obstruction :
    ∀ {eps : Q3Flag → ℝ}, signValues eps → tauOdd q3Tau eps →
      ¬ AdmissibleChannelKernel (signKernel eps)
  sector_dichotomy :
    (tauEven (ones Q3Flag)
      ∧ AdmissibleChannelKernel (signKernel (ones Q3Flag))
      ∧ signKernel (ones Q3Flag) = uniformReynolds Q3Flag)
    ∧ (tauOdd q3Tau flipParityChar
      ∧ ¬ AdmissibleChannelKernel (signKernel flipParityChar))
  conditional_closure :
    ∀ {eps : Q3Flag → ℝ}, B3SignCharacter eps → (∀ i j, eps i = eps j) →
      AdmissibleChannelKernel (signKernel eps)
        ∧ signKernel eps = uniformReynolds Q3Flag

theorem characterTrivialReductionCert_holds :
    Nonempty CharacterTrivialReductionCert :=
  ⟨{ invariant_free := by
        intro eps hchar; exact signChar_signKernel_b3Invariant hchar
     uniform_admissible := uniformReynolds_admissible
     reduction := by
        intro eps hchar; exact admissible_iff_trivial_character hchar
     flip_twist_obstruction := by
        intro eps hε hτ; exact tauOdd_flip_not_admissible hε hτ
     sector_dichotomy := boundary_sector_dichotomy
     conditional_closure := by
        intro eps hchar htriv
        exact charged_channel_admissible_of_trivial_character hchar htriv }⟩

end

end L1b5CharacterTrivialReduction
end Masses
end IndisputableMonolith
