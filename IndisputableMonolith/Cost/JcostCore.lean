import IndisputableMonolith.Cost

/-!
# J-Cost Core Compatibility Surface

The canonical J-cost definitions live in the root module
`IndisputableMonolith.Cost`.  Older Intelligence modules imported
`IndisputableMonolith.Cost.JcostCore`; this file now re-exports the root
surface and keeps the small set of additional instances/lemmas those modules
used.  It intentionally does not redefine `Jcost`, `AgreesOnExp`, or the other
root names, so importing both modules no longer creates environment conflicts.
-/

namespace IndisputableMonolith
namespace Cost

noncomputable section

@[simp] theorem Jcost_agrees_on_exp : AgreesOnExp Jcost := by
  intro t
  rfl

instance : AveragingAgree Jcost := ⟨Jcost_agrees_on_exp⟩

instance : SymmUnit Jcost where
  symmetric := by
    intro x hx
    exact Jcost_symm hx
  unit0 := Jcost_unit0

instance : AveragingDerivation Jcost where
  toSymmUnit := (inferInstance : SymmUnit Jcost)
  agrees := Jcost_agrees_on_exp

instance : JensenSketch Jcost where
  toSymmUnit := (inferInstance : SymmUnit Jcost)
  axis_upper := by
    intro t
    exact le_rfl
  axis_lower := by
    intro t
    exact le_rfl

/-- J-cost derivative: `d/dx J(x) = (1 - x⁻¹^2) / 2` away from zero. -/
lemma Jcost_deriv (x : ℝ) (hx : x ≠ 0) :
    deriv Jcost x = (1 - x⁻¹ ^ 2) / 2 := by
  unfold Jcost
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv hx
  have h3 : HasDerivAt (fun y : ℝ => y + y⁻¹) (1 + -(x ^ 2)⁻¹) x :=
    h1.add h2
  have h4 : HasDerivAt (fun y : ℝ => (y + y⁻¹) / 2)
      ((1 + -(x ^ 2)⁻¹) / 2) x :=
    h3.div_const 2
  have h5 : HasDerivAt (fun y : ℝ => (y + y⁻¹) / 2 - 1)
      ((1 + -(x ^ 2)⁻¹) / 2) x :=
    h4.sub_const 1
  rw [h5.deriv]
  field_simp [hx]
  ring

end

end Cost
end IndisputableMonolith
