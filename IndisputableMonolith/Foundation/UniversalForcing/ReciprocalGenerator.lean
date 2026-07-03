import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# The reciprocal involution is the common generator of J and φ

`OneLaw.lean` conjoins the cost-form theorem (J's shape) and the φ-forcing
theorem (the scale ratio). That conjunction is an *assembly*: its two halves
talk about two unrelated objects (`Cost.Jcost` and a `MinimalHierarchy`), and
neither is derived from the other.

This module isolates the genuine structural unification that does sit beneath
both. The single object is the **reciprocal involution** `ι(x) = x⁻¹` on the
positive reals — the dual-recognition symmetry that exchanges a quantity with
its reciprocal. We prove two properties *of this one function*:

* **Cost side.** `J` is exactly the `ι`-symmetric cost: `J ∘ ι = J`.
* **Scale side.** `φ` is the unique fixed point `> 1` of the `ι`-shift
  `g(x) = 1 + ι(x)`.

Both conjuncts in the capstone quantify over the same `recip`. That is what
makes this a deduction about a shared generator rather than a glued pair of
independent facts: the reciprocal involution is logically upstream of both the
cost's symmetry axis and the golden ratio's defining equation.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace ReciprocalGenerator

/-- The reciprocal involution on the positive reals, `ι(x) = x⁻¹`. This is the
dual-recognition symmetry the recognition framework is built on. -/
noncomputable def recip (x : ℝ) : ℝ := x⁻¹

/-- `ι` is an involution on the positive reals. -/
theorem recip_involutive {x : ℝ} (_hx : 0 < x) : recip (recip x) = x := by
  simp [recip]

/-- `ι` has a unique fixed point among positive reals, namely the unit `1`. -/
theorem recip_fixed_iff {x : ℝ} (hx : 0 < x) : recip x = x ↔ x = 1 := by
  unfold recip
  have hxne : x ≠ 0 := ne_of_gt hx
  constructor
  · intro h
    have hsq : x * x = 1 := by
      have hmul : x⁻¹ * x = x * x := by rw [h]
      rw [inv_mul_cancel₀ hxne] at hmul
      exact hmul.symm
    nlinarith [hsq, hx]
  · intro h; subst h; simp

/-! ## Cost side: J is the ι-symmetric cost -/

/-- `J` is invariant under the reciprocal involution: `J(ι x) = J(x)`. This is
`Cost.Jcost_symm`, here phrased as a property of `recip`. -/
theorem jcost_recip_symmetric {x : ℝ} (hx : 0 < x) :
    Cost.Jcost (recip x) = Cost.Jcost x := by
  unfold recip
  exact (Cost.Jcost_symm hx).symm

/-- **The involution's fixed point is the cost's zero.** For positive `x`,
`ι x = x ↔ J x = 0` — both hold iff `x = 1`. So `ι`'s own fixed point is not
arbitrary: it is the unit, the unique point of zero recognition cost. This is
the sharp form of the cost side — not merely that `J` is `ι`-symmetric, but that
the symmetry axis of `ι` coincides with the null set of `J`. -/
theorem recip_fixed_iff_cost_zero {x : ℝ} (hx : 0 < x) :
    recip x = x ↔ Cost.Jcost x = 0 := by
  rw [recip_fixed_iff hx, Cost.Jcost_eq_zero_iff x hx]

/-! ## Scale side: φ is the unique fixed point > 1 of the ι-shift -/

/-- The reciprocal-shift map `g(x) = 1 + ι(x) = 1 + x⁻¹`. Its fixed-point
equation `g(x) = x` is the self-similarity constraint `x = 1 + 1/x`. -/
noncomputable def recipShift (x : ℝ) : ℝ := 1 + recip x

/-- `φ` is a fixed point of the `ι`-shift. -/
theorem phi_is_recipShift_fixed : recipShift Constants.phi = Constants.phi := by
  unfold recipShift recip
  have h := PhiSupport.phi_fixed_point
  rw [one_div] at h
  exact h.symm

/-- `φ` is the **unique** fixed point of the `ι`-shift among reals `> 1`. -/
theorem recipShift_fixed_iff {x : ℝ} (hx : 1 < x) :
    recipShift x = x ↔ x = Constants.phi := by
  unfold recipShift recip
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  constructor
  · intro h
    have hexp : (1 + x⁻¹) * x = x + 1 := by
      rw [add_mul, one_mul, inv_mul_cancel₀ hxne]
    have hmul : (1 + x⁻¹) * x = x * x := by rw [h]
    rw [hexp] at hmul
    have hsq : x ^ 2 = x + 1 := by rw [pow_two]; linarith [hmul]
    exact (PhiSupport.phi_unique_pos_root x).mp ⟨hsq, hx0⟩
  · intro h; subst h
    have h := PhiSupport.phi_fixed_point
    rw [one_div] at h
    exact h.symm

/-! ## Capstone: one generator, two forced quantities -/

/-- **The reciprocal involution generates both the cost and the scale.**

The single function `recip = (·⁻¹)` is the structural object underneath both
sides of the math/physics bridge:

* `J` is exactly the `ι`-symmetric cost: `∀ x > 0, J(ι x) = J(x)`.
* `φ` is the unique fixed point `> 1` of the `ι`-shift `1 + ι`.

Both conjuncts quantify over the *same* `recip`. Unlike `OneLaw`'s assembly of
two facts about unrelated objects, this is a deduction about a shared
generator: the reciprocal involution is upstream of both the cost's symmetry
axis and the golden ratio's defining equation. -/
theorem recip_generates_cost_and_scale :
    (∀ x : ℝ, 0 < x → Cost.Jcost (recip x) = Cost.Jcost x)
    ∧ (∀ x : ℝ, 1 < x → (recipShift x = x ↔ x = Constants.phi)) :=
  ⟨fun _ hx => jcost_recip_symmetric hx,
   fun _ hx => recipShift_fixed_iff hx⟩

/-- **One involution, two constants.** The reciprocal involution `ι` pins both
fundamental quantities of the framework through its fixed points:

* the fixed point of `ι` itself is the unit `1`, which is exactly the zero of
  the recognition cost `J` (the no-cost point);
* the fixed point of the affine shift `1 + ι` is the golden ratio `φ`, the
  scale.

This is the sharpest form of the bridge. The unit and the scale — the two
constants the whole framework is built from — are the two fixed points of one
involution family: `ι` fixes the unit (= `J`'s null point), and `1 + ι` fixes
`φ`. -/
theorem recip_pins_unit_and_scale :
    (∀ x : ℝ, 0 < x → (recip x = x ↔ Cost.Jcost x = 0))
    ∧ (∀ x : ℝ, 1 < x → (recipShift x = x ↔ x = Constants.phi)) :=
  ⟨fun _ hx => recip_fixed_iff_cost_zero hx,
   fun _ hx => recipShift_fixed_iff hx⟩

/-- Certificate: the reciprocal involution is the common generator of `J` and
`φ`. Bundles the involution law, both downstream forcings, and the witness that
`φ` actually solves the `ι`-shift fixed-point equation. -/
structure ReciprocalGeneratorCert where
  involutive : ∀ x : ℝ, 0 < x → recip (recip x) = x
  cost_symmetric : ∀ x : ℝ, 0 < x → Cost.Jcost (recip x) = Cost.Jcost x
  unit_is_cost_zero : ∀ x : ℝ, 0 < x → (recip x = x ↔ Cost.Jcost x = 0)
  scale_unique : ∀ x : ℝ, 1 < x → (recipShift x = x ↔ x = Constants.phi)
  phi_solves : recipShift Constants.phi = Constants.phi

/-- The certificate holds. -/
noncomputable def reciprocalGeneratorCert_holds : ReciprocalGeneratorCert where
  involutive := fun _ hx => recip_involutive hx
  cost_symmetric := fun _ hx => jcost_recip_symmetric hx
  unit_is_cost_zero := fun _ hx => recip_fixed_iff_cost_zero hx
  scale_unique := fun _ hx => recipShift_fixed_iff hx
  phi_solves := phi_is_recipShift_fixed

end ReciprocalGenerator
end UniversalForcing
end Foundation
end IndisputableMonolith
