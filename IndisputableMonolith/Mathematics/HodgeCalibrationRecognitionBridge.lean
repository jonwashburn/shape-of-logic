import IndisputableMonolith.Mathematics.HodgeUnconditionalProofBoundary
import IndisputableMonolith.Cost

/-!
# Recognition-ratio bridge for the Hodge calibration defect

This module imports a genuinely proved fact into the Hodge diffuse-quotient
program and uses it to change the *shape* of the remaining gap.  It does not
prove Hodge, and it does not rename the missing lemma.

## The proved fact being imported

The canonical reciprocal cost `J(x) = ½(x + x⁻¹) − 1` is definite and coercive
on the positive reals.  In `IndisputableMonolith.Cost` these are theorems with
no `sorry` and no extra axioms:

* `Cost.Jcost_unit0`        : `J 1 = 0`;
* `Cost.Jcost_nonneg`       : `0 ≤ J x` for `0 < x`;
* `Cost.Jcost_pos_of_ne_one`: `0 < J x` for `0 < x`, `x ≠ 1`;
* `Cost.Jcost_eq_zero_iff`  : `J x = 0 ↔ x = 1` for `0 < x`.

## What the bridge does

`HodgeDiffuseQuotient.QuotientCalibrationLedger` carried the coercivity field
`positive_on_nonzero_diffuse` as a bare assumption.  Here that field is
*derived*, once the amortized defect is presented as the `J`-cost of a
*recognition ratio* on the algebraic quotient:

    amortizedDefect q  =  J (ratio q),    ratio : (Coh ⧸ A) → ℝ>0,  ratio 0 = 1.

Then, from the proved cost lemmas:

* `defect 0 = 0`            ⟸ `ratio 0 = 1` and `J 1 = 0`;
* `0 ≤ defect`              ⟸ `J ≥ 0` on positives;
* `q ≠ 0 → 0 < defect q`    ⟸ `ratio q ≠ 1` (faithfulness) and `J`-definiteness;
* `defect q = 0 ↔ q = 0`    ⟸ the same.

So `positive_on_nonzero_diffuse` is no longer ad hoc.  It factors as

    (proved cost definiteness)  ∘  (faithfulness of the recognition ratio).

In Recognition-Geometry language, faithfulness of `ratio` is injectivity of the
induced calibration recognizer on the algebraic quotient: it separates every
nonzero diffuse residual class from the cost-neutral value `1`.

## Honest status (read before reusing)

This does **not** reduce the difficulty.  An *arbitrary* faithful `ratio` exists
on any quotient that embeds in `ℝ>0` (e.g. any countable quotient) and proves
nothing.  The bridge is meaningful only when `ratio` realizes the *genuine*
geometric calibration defect `D` (its `J`-cost equals `D`), which is exactly
what `RealizesCalibrationDefect` records.  Under that realization:

* `faithful` for the real defect is the coercivity half — Hodge-level;
* `CalibrationConservativityTarget` (`ratio ≡ 1` on diffuse residuals) is the
  existence half, i.e. `inf_m defectZ(m·c)/m = 0`.

The conjunction is Hodge-equivalent.  This module supplies only the proved cost
structure and the algebraic plumbing; it constructs no geometric ratio.  The
`A = ⊤` witness at the end is a non-vacuity / consistency check, NOT a proof:
`⊤` is the degenerate "everything already algebraic" case.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeCalibrationRecognitionBridge

open HodgeDiffuseLocalization
open HodgeDiffuseQuotient
open HodgeUnconditionalProofBoundary

universe u

variable {Coh : Type u} [AddCommGroup Coh]

/-- A calibration recognition ratio on the algebraic quotient `Coh ⧸ A`.

`ratio` is the exponential of the amortized Kähler calibration defect: a
positive real attached to each quotient class, with the cost-neutral value `1`
on the algebraic (zero) class.  `faithful` is the geometric content — it says
the recognizer separates nonzero diffuse classes from `1`.  Supplying a *generic*
faithful ratio is the vacuous move flagged in the module docstring; the content
is that `ratio` realizes the genuine geometric defect (`RealizesCalibrationDefect`). -/
structure CalibrationRecognitionRatio (A : AddSubgroup Coh) where
  /-- The recognition ratio: exponential of the amortized calibration defect. -/
  ratio : AlgebraicQuotient A → ℝ
  /-- The ratio is strictly positive (it is an exponential). -/
  ratio_pos : ∀ q, 0 < ratio q
  /-- The algebraic (zero) class is cost-neutral. -/
  ratio_unit : ratio 0 = 1
  /-- Faithfulness: only the algebraic class is cost-neutral.  This is the
  Hodge-level coercivity content when `ratio` is the geometric defect. -/
  faithful : ∀ q, ratio q = 1 → q = 0

namespace CalibrationRecognitionRatio

variable {A : AddSubgroup Coh}

/-- The amortized calibration defect induced by the recognition ratio: the
canonical reciprocal cost of the ratio. -/
def defect (Rr : CalibrationRecognitionRatio A) (q : AlgebraicQuotient A) : ℝ :=
  Cost.Jcost (Rr.ratio q)

/-- The induced defect is nonnegative — directly from `Cost.Jcost_nonneg`. -/
theorem defect_nonneg (Rr : CalibrationRecognitionRatio A) (q : AlgebraicQuotient A) :
    0 ≤ Rr.defect q :=
  Cost.Jcost_nonneg (Rr.ratio_pos q)

/-- The defect vanishes on the algebraic (zero) class — from `ratio_unit` and
`Cost.Jcost_unit0`. -/
theorem defect_zero_class (Rr : CalibrationRecognitionRatio A) :
    Rr.defect 0 = 0 := by
  unfold defect
  rw [Rr.ratio_unit]
  exact Cost.Jcost_unit0

/-- **The imported coercivity.** A nonzero quotient class has strictly positive
defect.  This was a bare field of `QuotientCalibrationLedger`; here it is a
theorem, factored as faithfulness of the ratio composed with the proved
definiteness of the canonical cost (`Cost.Jcost_pos_of_ne_one`). -/
theorem defect_pos_of_ne_zero (Rr : CalibrationRecognitionRatio A)
    {q : AlgebraicQuotient A} (hq : q ≠ 0) : 0 < Rr.defect q := by
  have hne1 : Rr.ratio q ≠ 1 := fun h => hq (Rr.faithful q h)
  exact Cost.Jcost_pos_of_ne_one _ (Rr.ratio_pos q) hne1

/-- Definiteness of the induced defect: it vanishes exactly on the zero class. -/
theorem defect_eq_zero_iff (Rr : CalibrationRecognitionRatio A)
    (q : AlgebraicQuotient A) : Rr.defect q = 0 ↔ q = 0 := by
  constructor
  · intro h
    by_contra hq
    exact absurd h (ne_of_gt (Rr.defect_pos_of_ne_zero hq))
  · rintro rfl
    exact Rr.defect_zero_class

/-- Build a `QuotientCalibrationLedger` from a recognition ratio.  The previously
assumed positivity field `positive_on_nonzero_diffuse` is now discharged by
`defect_pos_of_ne_zero`. -/
def toLedger (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A) :
    QuotientCalibrationLedger A S where
  amortizedDefect := Rr.defect
  nonneg := Rr.defect_nonneg
  positive_on_nonzero_diffuse := fun _α hne => Rr.defect_pos_of_ne_zero hne

/-- Build the full `DiffuseCalibrationInterface` of the boundary module from a
recognition ratio.  The zero-normalization field is `defect_zero_class`. -/
def toInterface (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A) :
    DiffuseCalibrationInterface Coh where
  algebraicClasses := A
  siu := S
  ledger := Rr.toLedger S
  zero_defect_at_zero := Rr.defect_zero_class

/-- The defect realizes a target geometric defect `D` when its values agree with
`D` pointwise.  This is the field that carries the real content: `D` must be the
genuine amortized Kähler calibration defect, not a free choice. -/
def RealizesCalibrationDefect (Rr : CalibrationRecognitionRatio A)
    (D : AlgebraicQuotient A → ℝ) : Prop :=
  ∀ q, Rr.defect q = D q

end CalibrationRecognitionRatio

open CalibrationRecognitionRatio

/-- **Closure spine recovered, with positivity now proved.**  For the interface
built from a recognition ratio, rational Hodge is equivalent to calibration
conservativity on all diffuse residuals.  Compared to the boundary module, the
coercivity field is no longer assumed; it came from `Cost.Jcost_pos_of_ne_one`. -/
theorem hodge_iff_conservativity_via_ratio
    {A : AddSubgroup Coh} (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A) :
    (Rr.toInterface S).HodgeStatement ↔
      (Rr.toInterface S).CalibrationConservativityTarget :=
  (Rr.toInterface S).hodge_iff_calibrationConservativityTarget

/-- Conditional Hodge via the recognition ratio: if analytic completion is
conservative (zero amortized defect on every diffuse residual), every class is
algebraic.  The defect's definiteness does the killing. -/
theorem hodge_of_conservativity_via_ratio
    {A : AddSubgroup Coh} (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A)
    (hcons : (Rr.toInterface S).CalibrationConservativityTarget) :
    ∀ α : Coh, α ∈ A :=
  (Rr.toInterface S).hodge_of_calibrationConservativityTarget hcons

/-- **Conservativity recast in faithfulness language.**  For a recognition
ratio, "zero amortized defect on every diffuse residual" is exactly "the ratio
of every diffuse residual equals the cost-neutral value `1`."  This is the
Recognition-Geometry reading of the missing lemma: the calibration recognizer
cannot distinguish any diffuse residual from the algebraic class. -/
theorem conservativity_iff_ratio_one
    {A : AddSubgroup Coh} (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A) :
    (Rr.toInterface S).CalibrationConservativityTarget ↔
      ∀ α : Coh, Rr.ratio (diffuseResidualQuotient A S α) = 1 := by
  constructor
  · intro h α
    have hz : Cost.Jcost (Rr.ratio (diffuseResidualQuotient A S α)) = 0 := h α
    exact (Cost.Jcost_eq_zero_iff _ (Rr.ratio_pos _)).mp hz
  · intro h α
    show Cost.Jcost (Rr.ratio (diffuseResidualQuotient A S α)) = 0
    rw [h α]
    exact Cost.Jcost_unit0

/-- **The honest closure, with the geometric defect kept explicit.**  Suppose the
recognition ratio realizes the genuine geometric defect `D` (its `J`-cost equals
`D`), and `D` is conservative on diffuse residuals.  Then Hodge follows.

The two hypotheses are exactly the remaining geometric content:
`RealizesCalibrationDefect` ties `ratio` to the real defect (so the bridge is not
vacuous), and conservativity of `D` is `inf_m defectZ(m·c)/m = 0`.  Neither is
proved here. -/
theorem hodge_of_realizes_and_conservative
    {A : AddSubgroup Coh} (Rr : CalibrationRecognitionRatio A) (S : SiuData Coh A)
    {D : AlgebraicQuotient A → ℝ}
    (hreal : Rr.RealizesCalibrationDefect D)
    (hcons : ∀ α : Coh, D (diffuseResidualQuotient A S α) = 0) :
    ∀ α : Coh, α ∈ A := by
  apply hodge_of_conservativity_via_ratio Rr S
  intro α
  show Rr.defect (diffuseResidualQuotient A S α) = 0
  rw [hreal (diffuseResidualQuotient A S α)]
  exact hcons α

/-! ## Non-vacuity / consistency witness (NOT a proof of Hodge)

`A = ⊤` collapses the quotient to a point, so the constant ratio `1` is faithful
and every diffuse residual is the zero class.  This shows the recognition-ratio
interface is inhabited and the conditional theorems fire on a consistent model.
It is the degenerate case where every class is declared algebraic; it carries no
geometric information about genuine `(p,p)` classes. -/

section NonVacuity

/-- Every element of the quotient by `⊤` is zero. -/
theorem quotient_top_eq_zero (Coh : Type u) [AddCommGroup Coh]
    (q : AlgebraicQuotient (⊤ : AddSubgroup Coh)) : q = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  show quotientClass (⊤ : AddSubgroup Coh) x = 0
  exact (quotientClass_eq_zero_iff_mem (⊤ : AddSubgroup Coh) x).mpr (AddSubgroup.mem_top x)

/-- The trivial recognition ratio on the quotient by `⊤`. -/
def trivialRatio (Coh : Type u) [AddCommGroup Coh] :
    CalibrationRecognitionRatio (⊤ : AddSubgroup Coh) where
  ratio := fun _ => 1
  ratio_pos := fun _ => one_pos
  ratio_unit := rfl
  faithful := fun q _ => quotient_top_eq_zero Coh q

/-- The trivial Siu split for `A = ⊤`: analytic part is the identity, residual is
zero. -/
def trivialSiu (Coh : Type u) [AddCommGroup Coh] :
    SiuData Coh (⊤ : AddSubgroup Coh) where
  analytic := id
  diffuse := fun _ => 0
  sum := fun α => by simp
  analytic_mem := fun _ => AddSubgroup.mem_top _

/-- The recognition-ratio interface is inhabited (non-vacuity guard). -/
def trivialInterface (Coh : Type u) [AddCommGroup Coh] :
    DiffuseCalibrationInterface Coh :=
  (trivialRatio Coh).toInterface (trivialSiu Coh)

/-- Consistency: in the trivial model the Hodge statement holds. -/
theorem trivial_hodge_holds (Coh : Type u) [AddCommGroup Coh] :
    (trivialInterface Coh).HodgeStatement := by
  intro α
  exact AddSubgroup.mem_top α

/-- Consistency: in the trivial model calibration conservativity holds, so the
conditional theorem `hodge_of_conservativity_via_ratio` fires non-vacuously. -/
theorem trivial_conservativity (Coh : Type u) [AddCommGroup Coh] :
    (trivialInterface Coh).CalibrationConservativityTarget := by
  intro α
  have hz : diffuseResidualQuotient (⊤ : AddSubgroup Coh) (trivialSiu Coh) α = 0 :=
    quotient_top_eq_zero Coh _
  show (trivialRatio Coh).defect
      (diffuseResidualQuotient (⊤ : AddSubgroup Coh) (trivialSiu Coh) α) = 0
  rw [hz]
  exact (trivialRatio Coh).defect_zero_class

end NonVacuity

end HodgeCalibrationRecognitionBridge
end Mathematics
end IndisputableMonolith
