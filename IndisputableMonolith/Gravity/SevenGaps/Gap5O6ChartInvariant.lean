import IndisputableMonolith.Gravity.SevenGaps.Gap5ReparamAttackOnConstraintSector

/-!
# Campaign 2 Track C: O6, the first number the constraint sector could produce

The constraint sector currently buys a sign and a field-independence but no
number: `HKTKineticFromRecognitionCost` gives `cKin = 2 λ ^ 2 > 0` with the
chart constant `λ` free, and `2 λ ^ 2` absorbs whatever `λ` is. O6 asked whether
the *ratio* of the kinetic to the gradient coefficient in the ADM form is
chart-independent, on the reasoning that a chart-independent ratio would be the
first parameter-free number the sector produces.

The answer is no, and the reason identifies the right question instead. O6 asks
about the wrong invariant.

## What the rigidity theorem already pins

`HKTRigidityKineticNormalizedN2` concludes that a kinetic-normalized target has
the ADM shape with three coefficients and one relation between them:

    hamDensity = cKin * p ^ 2 + cGrad * (structureFunction * (Δa) ^ 2) + V a
    momDensity = cMom * p' * (Δa)
    cMom = 4 * cKin * cGrad

So the algebra pins one combination of `cKin` and `cGrad`, namely their product,
and leaves one free. The question is which combination is which.

## What is established

**§1. The product is determined and the ratio is not.** From the relation alone,
`cKin * cGrad = cMom / 4` always (`product_determined`), while two triples can
share a `cMom` and differ in ratio by any factor
(`ratio_not_determined`). So the ratio is exactly the free direction that
survives the rigidity theorem, and it cannot be a number.

**§2. Why, structurally.** The free direction is a chart rescaling. Sending
`a ↦ a / s` and `p ↦ s * p` preserves the symplectic pairing, scales `p ^ 2` by
`s ^ 2` and `(Δa) ^ 2` by `s ^ (-2)`, and so moves `(cKin, cGrad)` to
`(cKin / s ^ 2, cGrad * s ^ 2)`. The product is fixed and the ratio moves by
`s ^ 4`. The momentum density's own combination `p * (Δa)` is invariant under
the same rescaling, which is exactly why the algebra could pin `cMom` and
therefore the product, and could not pin the ratio.

That paragraph is the reading, not a theorem here: the scaling is stated on the
coefficients, and closure of the model class under the corresponding canonical
transformation is not formalized. Tagged DERIVED-UNFORMALIZED.

**§3. What recognition adds on top.** The recognition premise supplies
`cKin = 2 λ ^ 2 > 0`. That does not fix `λ`, so it does not fix `cKin`. But
composed with the algebra's relation it does transfer: the gradient coefficient
then has the sign of the momentum coefficient
(`recognition_transfers_sign_to_gradient`). So the sector buys a second sign it
did not have, which is a real if modest gain, and still no magnitude.

## The corrected successor

O6 should be restated. The first parameter-free number this sector could produce
is `cMom`, equivalently the product `cKin * cGrad`, because that is the
combination the constraint algebra pins and the chart cannot move. Asking
whether the ratio is a number was asking whether a gauge direction is physical,
and the answer to that was always going to be no.

Nothing here pins `cMom` either. That is the open item, and it is now a sharper
one than O6 was: find what fixes the single invariant, rather than hoping a
ratio of two free constants collapses.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap5O6

/-- The coefficient relation the rigidity theorem delivers. -/
def ADMCoefficients (cKin cGrad cMom : ℝ) : Prop :=
  cKin ≠ 0 ∧ cGrad ≠ 0 ∧ cMom = 4 * cKin * cGrad

/-! ## §1. The product is determined, the ratio is not -/

/-- **The product is a function of what the algebra pins.** -/
theorem product_determined {cKin cGrad cMom : ℝ}
    (h : ADMCoefficients cKin cGrad cMom) : cKin * cGrad = cMom / 4 := by
  obtain ⟨_, _, hrel⟩ := h
  rw [hrel]; ring

/-- **The ratio is not.** Two coefficient triples with the same `cMom` whose
kinetic-to-gradient ratios differ by a factor of four. Scaling the example
shows the ratio takes every positive value at fixed `cMom`. -/
theorem ratio_not_determined :
    ADMCoefficients 1 1 4 ∧ ADMCoefficients 2 (1 / 2) 4
      ∧ (1 : ℝ) / 1 ≠ 2 / (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num, by norm_num⟩, by norm_num⟩

/-- The general statement, which is what makes the ratio a gauge direction
rather than merely underdetermined: at a fixed positive `cMom` the ratio takes
*every* positive value. -/
theorem ratio_takes_every_value {cMom : ℝ} (hMom : 0 < cMom) (t : ℝ) (ht : 0 < t) :
    ∃ cKin cGrad : ℝ, ADMCoefficients cKin cGrad cMom ∧ cKin / cGrad = t := by
  have hquot : 0 < cMom / (4 * t) := by positivity
  set g : ℝ := Real.sqrt (cMom / (4 * t)) with hg
  have hgpos : 0 < g := Real.sqrt_pos.mpr hquot
  have hgsq : g ^ 2 = cMom / (4 * t) := Real.sq_sqrt (le_of_lt hquot)
  refine ⟨t * g, g, ⟨by positivity, ne_of_gt hgpos, ?_⟩, ?_⟩
  · rw [show 4 * (t * g) * g = 4 * t * g ^ 2 by ring, hgsq]
    field_simp
  · field_simp

/-! ## §3. Recognition transfers the sign it fixes -/

/-- **The recognition premise gives the gradient sector a sign.** `cKin` is
`2 λ ^ 2` and so positive, and the algebra's relation then makes `cGrad`
positive exactly when `cMom` is. The sector buys a second sign; it still buys no
magnitude. -/
theorem recognition_transfers_sign_to_gradient
    {lam cGrad cMom : ℝ} (hlam : lam ≠ 0)
    (h : ADMCoefficients (2 * lam ^ 2) cGrad cMom) :
    (0 < cMom ↔ 0 < cGrad) := by
  obtain ⟨_, _, hrel⟩ := h
  have hsq : 0 < lam ^ 2 := by rcases hlam.lt_or_lt with h' | h' <;> nlinarith
  constructor
  · intro hM
    rw [hrel] at hM
    by_contra hc
    push_neg at hc
    nlinarith [hsq, hc]
  · intro hG
    rw [hrel]
    nlinarith [hsq, hG]

/-! ## §4. Named package -/

/-- **Track C verdict.** O6 asked whether the kinetic-to-gradient ratio is
chart-independent. It is not: it is the one direction the rigidity relation
leaves free. The product is the invariant, and pinning it, not the ratio, is the
route to the sector's first number. -/
def gap5_o6_ratio_is_free_product_is_the_invariant : Prop :=
  (∀ {cKin cGrad cMom : ℝ}, ADMCoefficients cKin cGrad cMom →
      cKin * cGrad = cMom / 4)
  ∧ (ADMCoefficients 1 1 4 ∧ ADMCoefficients 2 (1 / 2) 4
      ∧ (1 : ℝ) / 1 ≠ 2 / (1 / 2))
  ∧ (∀ {lam cGrad cMom : ℝ}, lam ≠ 0 →
      ADMCoefficients (2 * lam ^ 2) cGrad cMom → (0 < cMom ↔ 0 < cGrad))

theorem gap5_o6_ratio_is_free_product_is_the_invariant_holds :
    gap5_o6_ratio_is_free_product_is_the_invariant :=
  ⟨fun h => product_determined h,
   ratio_not_determined,
   fun hlam h => recognition_transfers_sign_to_gradient hlam h⟩

/-! ## §5. Axiom audit -/

section Audit

#print axioms product_determined
#print axioms ratio_takes_every_value
#print axioms ratio_not_determined
#print axioms recognition_transfers_sign_to_gradient
#print axioms gap5_o6_ratio_is_free_product_is_the_invariant_holds

end Audit

end Gap5O6
end SevenGaps
end Gravity
end IndisputableMonolith
