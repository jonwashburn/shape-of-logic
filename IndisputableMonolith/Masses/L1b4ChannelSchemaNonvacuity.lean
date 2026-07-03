import Mathlib
import IndisputableMonolith.Masses.L1bChargedChannelAdmissible

/-!
# L1b4 Channel-Schema Non-Vacuity (Track B, first step)

This module discharges the panel-greenlit first step of the Track-B physical
bridge: **lock the operator class = character projectors of B3 representations,
and lake-certify that the schema is non-vacuous by instantiating it at the
tau-odd flip-parity character.**

The result is a mechanical localization of the physical wall. It proves that the
tau-odd flip-parity character projector `signKernel flipParityChar` (the excluded
member `Sigma_chi` of Track A's killer gate):

* satisfies conjunct (i)   `b3Invariant`            (NEW here);
* satisfies conjunct (ii)  `K * K = K`              (`signKernel_idempotent`);
* satisfies conjunct (iii) `diagonalContent K = 1`  (`signKernel_diagonalContent_one`);
* FAILS   conjunct (iv)    `entrywiseNonneg K`      (`flipParitySignKernel_not_entrywiseNonneg`);
* is genuinely `≠ uniformReynolds Q3Flag`.

Consequences (all THEOREM, axiom-clean modulo the finite `native_decide`
machinery inherited from the B3 carrier):

1. `AdmissibleChannelKernel` is **non-vacuous in the strong sense**: there is a
   B3-invariant, idempotent, content-one kernel that is NOT admissible and NOT
   the uniform Reynolds projector. So conjuncts (i)-(iii) do NOT force `R`; the
   finite-algebra uniqueness theorem `admissibleChannelKernel_unique` is not
   vacuously true.
2. The **binding constraint of the physical bridge is precisely conjunct (iv)**
   (entrywise nonnegativity). (i)-(iii) are free for the character-projector
   class; the entire Track-B physical claim collapses to "the physical channel
   is entrywise nonnegative", i.e. classical/Perron-Frobenius ledger positivity
   selects the trivial representation over the tau-odd one.

Honest boundary: this does NOT define or identify the physical charged-lepton
channel, and does NOT prove it satisfies conjunct (iv). It only fixes the
operator class, certifies the schema is non-vacuous, and localizes the remaining
physical content to a single conjunct. L1b (the physical admissibility of the
charged channel) and L1 (the full mass bridge) remain OPEN.

Anti-circularity: nothing here depends on `uniformReynolds` or
`b3ReynoldsAverage` as a *definition* of the excluded member; the excluded member
is built independently as `characterProjector flipParityChar`, and its exclusion
is derived, not assumed.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1b4ChannelSchemaNonvacuity

open L1b1UniformReynoldsEngine
open L1b2SignKernelExclusion
open L1b3Q3FlagCarrier
open L1bChargedChannelAdmissible

noncomputable section

local instance : Nonempty Q3Flag := ⟨b3Id⟩

/--
Conjunct (i) for the tau-odd flip-parity character projector.

Any character projector built from a one-dimensional B3 sign character is
B3-invariant on the principal carrier, because the character is a homomorphism
to `{±1}` and so squares to `1`:
`K(g·x, g·y) = c⁻¹ χ(g·x) χ(g·y) = c⁻¹ χ(g)² χ(x) χ(y) = c⁻¹ χ(x) χ(y) = K(x,y)`.

This is the reason conjuncts (i)-(iii) are *free* for the character-projector
operator class.
-/
theorem flipParitySignKernel_b3Invariant :
    b3Invariant (signKernel flipParityChar) := by
  intro g x y
  have hx : flipParityChar (b3Act g x) = flipParityChar g * flipParityChar x :=
    flipParityChar_mul g x
  have hy : flipParityChar (b3Act g y) = flipParityChar g * flipParityChar y :=
    flipParityChar_mul g y
  have hg2 : flipParityChar g * flipParityChar g = 1 :=
    sign_mul_self flipParityChar_signValues g
  rw [signKernel_apply flipParityChar_signValues (b3Act g x) (b3Act g y),
      signKernel_apply flipParityChar_signValues x y, hx, hy]
  linear_combination
    ((Fintype.card Q3Flag : ℝ)⁻¹ * flipParityChar x * flipParityChar y) * hg2

/--
The tau-odd flip-parity character projector satisfies conjuncts (i), (ii), (iii)
and FAILS conjunct (iv). This is the non-vacuity witness for the schema.
-/
theorem flipParitySchema_i_ii_iii_not_iv :
    b3Invariant (signKernel flipParityChar) ∧
      (signKernel flipParityChar) * (signKernel flipParityChar)
        = signKernel flipParityChar ∧
      diagonalContent (signKernel flipParityChar) = 1 ∧
      ¬ entrywiseNonneg (signKernel flipParityChar) := by
  refine ⟨flipParitySignKernel_b3Invariant, ?_, ?_, ?_⟩
  · exact signKernel_idempotent flipParityChar_signValues
  · exact signKernel_diagonalContent_one flipParityChar_signValues
  · exact flipParitySignKernel_not_entrywiseNonneg

/--
The tau-odd flip-parity character projector is NOT admissible: it satisfies
(i)-(iii) but fails (iv). Hence conjunct (iv) is the *binding* constraint.
-/
theorem flipParitySchema_not_admissible :
    ¬ AdmissibleChannelKernel (signKernel flipParityChar) := by
  intro h
  exact flipParitySignKernel_not_entrywiseNonneg h.2.2.2

/--
The excluded member genuinely differs from the uniform Reynolds projector.
Together with `flipParitySchema_i_ii_iii_not_iv` this shows conjuncts (i)-(iii)
do NOT force the kernel to be `R`: the forcing to `R` is supplied by conjunct
(iv), not by invariance/idempotence/content alone.
-/
theorem flipParitySchema_ne_uniformReynolds :
    signKernel flipParityChar ≠ uniformReynolds Q3Flag := by
  intro h
  apply flipParitySignKernel_not_entrywiseNonneg
  rw [h]
  exact uniformReynolds_entrywiseNonneg

/--
Strong non-vacuity of `AdmissibleChannelKernel`: there exists a kernel on the
principal B3 carrier that is B3-invariant, idempotent, has diagonal content one,
is NOT admissible, and is NOT the uniform Reynolds projector.

This certifies that the finite-algebra uniqueness theorem is not vacuously true
and that the physical bridge collapses to conjunct (iv) alone.
-/
theorem admissibleChannelKernel_strongly_nonvacuous :
    ∃ K : Matrix Q3Flag Q3Flag ℝ,
      b3Invariant K ∧ K * K = K ∧ diagonalContent K = 1 ∧
        ¬ AdmissibleChannelKernel K ∧ K ≠ uniformReynolds Q3Flag := by
  refine ⟨signKernel flipParityChar, ?_, ?_, ?_, ?_, ?_⟩
  · exact flipParitySignKernel_b3Invariant
  · exact signKernel_idempotent flipParityChar_signValues
  · exact signKernel_diagonalContent_one flipParityChar_signValues
  · exact flipParitySchema_not_admissible
  · exact flipParitySchema_ne_uniformReynolds

/-- L1b4 non-vacuity certificate. This is NOT an L1b or L1 closure. -/
structure ChannelSchemaNonvacuityCert where
  binding_conjunct_i :
    b3Invariant (signKernel flipParityChar)
  free_conjunct_ii :
    (signKernel flipParityChar) * (signKernel flipParityChar)
      = signKernel flipParityChar
  free_conjunct_iii :
    diagonalContent (signKernel flipParityChar) = 1
  fails_conjunct_iv :
    ¬ entrywiseNonneg (signKernel flipParityChar)
  not_admissible :
    ¬ AdmissibleChannelKernel (signKernel flipParityChar)
  ne_uniform :
    signKernel flipParityChar ≠ uniformReynolds Q3Flag
  strongly_nonvacuous :
    ∃ K : Matrix Q3Flag Q3Flag ℝ,
      b3Invariant K ∧ K * K = K ∧ diagonalContent K = 1 ∧
        ¬ AdmissibleChannelKernel K ∧ K ≠ uniformReynolds Q3Flag

theorem channelSchemaNonvacuityCert_holds :
    Nonempty ChannelSchemaNonvacuityCert :=
  ⟨{ binding_conjunct_i := flipParitySignKernel_b3Invariant
     free_conjunct_ii := signKernel_idempotent flipParityChar_signValues
     free_conjunct_iii := signKernel_diagonalContent_one flipParityChar_signValues
     fails_conjunct_iv := flipParitySignKernel_not_entrywiseNonneg
     not_admissible := flipParitySchema_not_admissible
     ne_uniform := flipParitySchema_ne_uniformReynolds
     strongly_nonvacuous := admissibleChannelKernel_strongly_nonvacuous }⟩

end

end L1b4ChannelSchemaNonvacuity
end Masses
end IndisputableMonolith
