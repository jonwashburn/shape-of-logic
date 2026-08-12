import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-!
# Gap 1, O4: do hinge areas force class lengths?

The four-dimensional weight obstruction is stated about **class lengths**, but
the Regge action pairs deficit angles with **hinge areas**. Until the gap
between the two closes, the obstruction's honest scope is class lengths and not
the action. This module closes it, positively and with the residue named.

## The geometry that makes the question tractable

In the Freudenthal (Kuhn) triangulation of the four-dimensional cubic lattice a
simplex has vertices at the partial sums of a permutation of the coordinate
directions. Two vertices of a hinge therefore differ by the indicator vector of
a set of directions, and the three edges of a hinge are `1_S`, `1_T` and
`1_{S ∪ T}` for **disjoint** nonempty `S` and `T`. Disjoint supports are
orthogonal, so every hinge is right-angled and Heron's formula collapses:

    area = (1/2) * ℓ_S * ℓ_T,   ℓ_S = √|S|.

The hinge measure is a product of two class lengths, never a sum. That is the
fact that decides O4.

## What is proved

`product_rigidity`: any positive weight assignment reproducing every hinge area
agrees with the geometric class length on every class except the body diagonal.
The proof is short because three pairwise disjoint singletons give three
equations in three unknowns whose only positive solution is one.

`fullClass_area_free`: the body diagonal really is free. It is the only nonempty
subset of four directions with no nonempty disjoint partner, so it appears in no
area equation, and any positive value for it satisfies the whole system.

`areas_force_irrational_class_lengths`: the classes the areas do force are
exactly those of size at most three, which carry `1`, `√2` and `√3`. Those are
the three lengths the counting obstruction's irrationality collision runs on.
The one class the areas leave free has length `2`, and
`Gap1Counting4DObstruction` already proves that class inert: it lands in the
rational part of the collision and never touches either colliding condition.

So the obstruction transports from class lengths to hinge areas, and the single
degree of freedom the transport loses is the one degree of freedom the
obstruction never used.

## Scope

The product form uses the lattice's own orthogonality. A mechanism proposing
hinges that are not right-angled is outside this result, and so is any
reading in which the areas are matched only up to an overall scale that is
allowed to differ between hinges.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap1HingeAreas

open Finset

noncomputable section

/-! ## §1. Heron, and its collapse on a right-angled hinge -/

/-- Sixteen times the squared area of a triangle with squared side lengths
`X`, `Y`, `Z`. This is Heron's formula in the form that stays polynomial. -/
def heron16 (X Y Z : ℝ) : ℝ :=
  2 * (X * Y + Y * Z + Z * X) - (X ^ 2 + Y ^ 2 + Z ^ 2)

/-- **The collapse.** When the third squared side is the sum of the other two,
which is exactly the Pythagorean condition, Heron's formula degenerates to a
product. No square root survives except the one in the two leg lengths. -/
theorem heron16_right (X Y : ℝ) : heron16 X Y (X + Y) = 4 * (X * Y) := by
  unfold heron16
  ring

/-- The right angle is the unique configuration attaining that area: given the
two legs, the hypotenuse is pinned rather than pinned up to two choices. This is
why matching an area cannot silently change a hinge's shape. -/
theorem heron16_right_unique (X Y Z : ℝ) (h : heron16 X Y Z = 4 * (X * Y)) :
    Z = X + Y := by
  have hsq : (Z - (X + Y)) ^ 2 = 0 := by
    unfold heron16 at h
    linarith [h]
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  linarith

/-! ## §2. Classes, lengths, and the hinge incidence -/

/-- The squared length of the displacement class of a set of directions. The
displacement is the indicator vector `1_S`, so its squared length is `|S|`. -/
def geomSq (S : Finset (Fin 4)) : ℝ := (S.card : ℝ)

/-- The class length `ℓ_S = √|S|`. -/
def geomLen (S : Finset (Fin 4)) : ℝ := Real.sqrt (S.card : ℝ)

theorem geomLen_nonneg (S : Finset (Fin 4)) : 0 ≤ geomLen S := Real.sqrt_nonneg _

theorem geomLen_sq (S : Finset (Fin 4)) : geomLen S ^ 2 = geomSq S :=
  Real.sq_sqrt (by positivity)

theorem geomLen_singleton (a : Fin 4) : geomLen {a} = 1 := by
  simp [geomLen]

/-- The body diagonal has rational length `2`. -/
theorem geomLen_univ : geomLen (univ : Finset (Fin 4)) = 2 := by
  have hcard : (univ : Finset (Fin 4)).card = 4 := by simp
  rw [geomLen, hcard]
  rw [show ((4 : ℕ) : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- A hinge of the Freudenthal lattice, spanned by two disjoint direction sets.
Its squared sides are `|S|`, `|T|` and `|S| + |T|`. -/
theorem hinge_heron16 (S T : Finset (Fin 4)) (h : Disjoint S T) :
    heron16 (geomSq S) (geomSq T) (geomSq (S ∪ T)) = 4 * ((S.card : ℝ) * (T.card : ℝ)) := by
  have hcard : ((S ∪ T).card : ℝ) = (S.card : ℝ) + (T.card : ℝ) := by
    rw [Finset.card_union_of_disjoint h]
    push_cast
    ring
  unfold geomSq
  rw [hcard]
  exact heron16_right _ _

/-- **The hinge measure is a product of two class lengths.** -/
theorem hinge_area_eq_product (S T : Finset (Fin 4)) (h : Disjoint S T) :
    Real.sqrt (heron16 (geomSq S) (geomSq T) (geomSq (S ∪ T))) / 4
      = geomLen S * geomLen T / 2 := by
  rw [hinge_heron16 S T h]
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hst : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  rw [Real.sqrt_mul h4, Real.sqrt_mul hst,
    show Real.sqrt (4 : ℝ) = 2 by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  unfold geomLen
  ring

/-! ## §3. Rigidity: the areas force twelve of the fifteen class lengths -/

/-- The hinge-area system. A weight assignment `w` reproduces every hinge area
of the lattice exactly when the product of the two leg weights matches, for
every pair of disjoint nonempty direction sets. -/
def ReproducesHingeAreas (w : Finset (Fin 4) → ℝ) : Prop :=
  ∀ S T : Finset (Fin 4), S.Nonempty → T.Nonempty → Disjoint S T →
    w S * w T = geomLen S * geomLen T

/-- The geometric assignment reproduces the areas, trivially. Stated so that the
system below is known to have at least one solution. -/
theorem geomLen_reproducesHingeAreas : ReproducesHingeAreas geomLen :=
  fun _ _ _ _ _ => rfl

private lemma singleton_eq_one_of_three (w : Finset (Fin 4) → ℝ)
    (hpos : ∀ S : Finset (Fin 4), S.Nonempty → 0 < w S)
    (harea : ReproducesHingeAreas w) (a b c : Fin 4)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : w {a} = 1 := by
  have hne : ∀ x : Fin 4, ({x} : Finset (Fin 4)).Nonempty := fun x => ⟨x, mem_singleton_self x⟩
  have hone : ∀ x y : Fin 4, x ≠ y → w {x} * w {y} = 1 := by
    intro x y hxy
    have hd : Disjoint ({x} : Finset (Fin 4)) {y} := Finset.disjoint_singleton.mpr hxy
    have := harea {x} {y} (hne x) (hne y) hd
    rwa [geomLen_singleton, geomLen_singleton, one_mul] at this
  have hab' := hone a b hab
  have hac' := hone a c hac
  have hbc' := hone b c hbc
  have hsq : w {a} ^ 2 = 1 := by
    have hbpos := hpos {b} (hne b)
    have hcpos := hpos {c} (hne c)
    nlinarith [hab', hac', hbc']
  have hapos := hpos {a} (hne a)
  nlinarith [hsq, hapos]

/-- Every singleton class has weight one. Three pairwise distinct directions
exist in four dimensions, which is all the argument needs. -/
theorem singleton_eq_one (w : Finset (Fin 4) → ℝ)
    (hpos : ∀ S : Finset (Fin 4), S.Nonempty → 0 < w S)
    (harea : ReproducesHingeAreas w) (a : Fin 4) : w {a} = 1 := by
  fin_cases a
  · exact singleton_eq_one_of_three w hpos harea 0 1 2 (by decide) (by decide) (by decide)
  · exact singleton_eq_one_of_three w hpos harea 1 0 2 (by decide) (by decide) (by decide)
  · exact singleton_eq_one_of_three w hpos harea 2 0 1 (by decide) (by decide) (by decide)
  · exact singleton_eq_one_of_three w hpos harea 3 0 1 (by decide) (by decide) (by decide)

/-- **PRODUCT RIGIDITY.** Reproducing the hinge areas forces the geometric class
length on every class that has a disjoint partner, that is, on every class other
than the body diagonal. -/
theorem product_rigidity (w : Finset (Fin 4) → ℝ)
    (hpos : ∀ S : Finset (Fin 4), S.Nonempty → 0 < w S)
    (harea : ReproducesHingeAreas w) (S : Finset (Fin 4))
    (hS : S.Nonempty) (hne : S ≠ univ) : w S = geomLen S := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 4, a ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact hne (Finset.eq_univ_iff_forall.mpr hcon)
  have hd : Disjoint S ({a} : Finset (Fin 4)) := Finset.disjoint_singleton_right.mpr ha
  have h := harea S {a} hS ⟨a, mem_singleton_self a⟩ hd
  rw [singleton_eq_one w hpos harea a, geomLen_singleton, mul_one, mul_one] at h
  exact h

/-! ## §4. The residue: the body diagonal is genuinely free -/

/-- The body diagonal has no nonempty disjoint partner, so it appears in no
hinge-area equation. -/
theorem univ_no_disjoint_partner (T : Finset (Fin 4)) (hT : T.Nonempty) :
    ¬ Disjoint (univ : Finset (Fin 4)) T := by
  intro hd
  obtain ⟨x, hx⟩ := hT
  exact absurd (Finset.disjoint_left.mp hd (mem_univ x)) (not_not.mpr hx)

/-- **THE FREEDOM IS REAL.** Moving the body diagonal's weight to `t` and
leaving every other class alone still reproduces every hinge area. So the areas
do not determine that one class, and the rigidity above is sharp rather than
merely the best the proof could reach. Positivity of `t` is not needed, which
says the areas constrain that class not weakly but not at all. -/
theorem fullClass_area_free (t : ℝ) :
    ReproducesHingeAreas (fun S => if S = univ then t else geomLen S) := by
  intro S T hS hT hd
  have hSne : S ≠ univ := by
    intro h
    exact univ_no_disjoint_partner T hT (h ▸ hd)
  have hTne : T ≠ univ := by
    intro h
    exact univ_no_disjoint_partner S hS (h ▸ hd.symm)
  simp [hSne, hTne]

/-! ## §5. O4: the obstruction transports -/

/-- Any class of size at most three is not the body diagonal. -/
theorem ne_univ_of_card_le_three (S : Finset (Fin 4)) (h : S.card ≤ 3) : S ≠ univ := by
  intro hS
  rw [hS] at h
  simp at h

/-- **O4.** Reproducing the hinge areas of the four-dimensional Freudenthal
lattice forces the class length of every class of size at most three, that is,
of every class carrying `1`, `√2` or `√3`. Those are exactly the three lengths
the counting obstruction's irrationality collision runs on. -/
theorem areas_force_irrational_class_lengths (w : Finset (Fin 4) → ℝ)
    (hpos : ∀ S : Finset (Fin 4), S.Nonempty → 0 < w S)
    (harea : ReproducesHingeAreas w) (S : Finset (Fin 4))
    (hS : S.Nonempty) (hcard : S.card ≤ 3) : w S = Real.sqrt (S.card : ℝ) :=
  product_rigidity w hpos harea S hS (ne_univ_of_card_le_three S hcard)

/-- The single class the areas leave free has rational length, which is the
class `Gap1Counting4DObstruction` already proves inert. -/
theorem free_class_length_is_rational : geomLen (univ : Finset (Fin 4)) = 2 :=
  geomLen_univ

/-- **The transport statement.** Hinge-area data determines every class length
whose value is irrational, and determines nothing about the one class whose
value is rational. -/
def gap1_hinge_areas_force_class_lengths : Prop :=
  (∀ w : Finset (Fin 4) → ℝ, (∀ S : Finset (Fin 4), S.Nonempty → 0 < w S) →
      ReproducesHingeAreas w →
      ∀ S : Finset (Fin 4), S.Nonempty → S.card ≤ 3 → w S = Real.sqrt (S.card : ℝ))
    ∧ (∀ t : ℝ, ReproducesHingeAreas (fun S => if S = univ then t else geomLen S))

theorem gap1_hinge_areas_force_class_lengths_holds :
    gap1_hinge_areas_force_class_lengths :=
  ⟨fun w hpos harea S hS hcard => areas_force_irrational_class_lengths w hpos harea S hS hcard,
    fullClass_area_free⟩

end

end Gap1HingeAreas
end SevenGaps
end Gravity
end IndisputableMonolith
