import Mathlib

/-!
  ScaleHomogeneityNoGo.lean

  The boundary theorem of the forced skeleton, in neutral vocabulary.

  The uniqueness chain (T-2 through T8) derives the skeleton of the theory
  without a scale. This module proves, once and abstractly, why the chain
  cannot go further on its own: no selection criterion that is blind to
  joint rescaling of a posted value and its carrier can fix an absolute
  value for a scale-invariant target. Any such criterion that accepts the
  intended witness also accepts a doubled decoy whose posted value misses
  the target. Hence at least one scale-bearing input is required.

  The statement is deliberately type-agnostic: the carrier `X` is any type
  equipped with a positive-real scaling action. Two witnesses built from
  ordinary mathematical types (real pairs with a squared ratio, and
  eight-component complex vectors with a probability weight) instantiate
  the hypotheses, so the no-go is a general fact about scale-invariant
  selection, not a property of any particular carrier.

  This is the canonical public form of the boundary theorem used in the
  paper "Recognition Composition and the Forced Skeleton". The ledger
  instantiation (`MassGenesis.T10JointScaleHomogeneityNoGo`) lives in the
  full Recognition Science library and is an instance of the class theorem
  proved here.

  The module carries the theorem in two forms. `ScaleHomogeneityNoGo`
  proves the joint-selector form (a posted value against a
  scale-invariant target). `ScaleHomogeneityNoGo.AmplitudeForm` proves
  the paper's S5 statement verbatim: over a scaled configuration space
  (a `ℝ_{>0}`-action with a degree-one homogeneous amplitude), an
  invariant selector's selected amplitude set is contained in `{0}` or
  contains every positive real, with the positive-quadrant witness
  pinning the scale-invariant ratio `a/b` to `2` while leaving the
  amplitude free.

  No `sorry`; no new Lean `axiom`.
-/

namespace IndisputableMonolith
namespace Foundation

universe u

/-- A positive-real scaling action on a carrier `X`. The action laws are
recorded so that instances cannot smuggle in state-dependent rescaling. -/
structure ScaleAction (X : Type u) where
  scale : ℝ → X → X
  scale_one : ∀ x, scale 1 x = x
  scale_mul : ∀ c d x, scale (c * d) x = scale c (scale d x)

namespace ScaleHomogeneityNoGo

noncomputable section

variable {X : Type u} (act : ScaleAction X)

/-- A candidate selector is invariant under joint positive rescaling of the
posted value and the carrier. -/
def IsJointScaleInvariantSelector (S : ℝ → X → Prop) : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (a : ℝ) (x : X), S a x ↔ S (c * a) (act.scale c x)

/-- A target functional is scale-invariant when rescaling the carrier does
not change its value. -/
def IsScaleInvariant (f : X → ℝ) : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ x, f (act.scale c x) = f x

/-- Main class theorem (the doubling decoy): no joint-scale-invariant
selector that accepts the intended witness can force the posted value to
the scale-invariant target. Proof: from `S (f x₀) x₀` joint invariance
gives `S (2 * f x₀) (scale 2 x₀)`, and scale invariance of `f` gives
`f (scale 2 x₀) = f x₀ ≠ 2 * f x₀`. -/
theorem no_scaleInvariantSelector_forces_value
    (S : ℝ → X → Prop) (hS : IsJointScaleInvariantSelector act S)
    (f : X → ℝ) (hf : IsScaleInvariant act f)
    (x₀ : X) (hpos : 0 < f x₀) (h₀ : S (f x₀) x₀) :
    ¬ ∀ (a : ℝ) (x : X), S a x → a = f x := by
  intro hall
  have h2 : S (2 * f x₀) (act.scale 2 x₀) :=
    (hS 2 (by norm_num) (f x₀) x₀).mp h₀
  have hfx : f (act.scale 2 x₀) = f x₀ := hf 2 (by norm_num) x₀
  have heq := hall _ _ h2
  rw [hfx] at heq
  linarith [hpos]

/-- Admission-gate export: any selector that does force the posted value on
the intended witness cannot be joint-scale invariant. -/
theorem forcingSelector_not_jointScaleInvariant
    (S : ℝ → X → Prop) (f : X → ℝ) (hf : IsScaleInvariant act f)
    (x₀ : X) (hpos : 0 < f x₀) (h₀ : S (f x₀) x₀)
    (hforces : ∀ (a : ℝ) (x : X), S a x → a = f x) :
    ¬ IsJointScaleInvariantSelector act S := by
  intro hS
  exact no_scaleInvariantSelector_forces_value act S hS f hf x₀ hpos h₀ hforces

/-- The positivity selector: accepts exactly the positive posted values.
It ignores the carrier, so it is joint-scale invariant for any action. -/
def PositivitySelector : ℝ → X → Prop := fun a _ => 0 < a

theorem positivitySelector_jointScaleInvariant :
    IsJointScaleInvariantSelector act (PositivitySelector (X := X)) := by
  intro c hc a x
  constructor
  · exact mul_pos hc
  · exact fun h => pos_of_mul_pos_right h (le_of_lt hc)

/-- Non-vacuity: the positivity selector lies in the class, accepts the
intended witness whenever the target is positive there, and therefore
cannot force the target value. -/
theorem positivitySelector_does_not_force_value
    (f : X → ℝ) (hf : IsScaleInvariant act f)
    (x₀ : X) (hpos : 0 < f x₀) :
    ¬ ∀ (a : ℝ) (x : X), PositivitySelector a x → a = f x :=
  no_scaleInvariantSelector_forces_value act _
    (positivitySelector_jointScaleInvariant act) f hf x₀ hpos hpos

/-- Certificate bundling the class wall, the admission export, and the
non-vacuity witness. -/
structure ScaleHomogeneityNoGoCert (X : Type u) (act : ScaleAction X) : Prop where
  class_wall :
    ∀ (S : ℝ → X → Prop), IsJointScaleInvariantSelector act S →
      ∀ (f : X → ℝ), IsScaleInvariant act f →
        ∀ (x₀ : X), 0 < f x₀ → S (f x₀) x₀ →
          ¬ ∀ (a : ℝ) (x : X), S a x → a = f x
  admission_export :
    ∀ (S : ℝ → X → Prop) (f : X → ℝ), IsScaleInvariant act f →
      ∀ (x₀ : X), 0 < f x₀ → S (f x₀) x₀ →
        (∀ (a : ℝ) (x : X), S a x → a = f x) →
          ¬ IsJointScaleInvariantSelector act S
  class_nonempty : ∃ S, IsJointScaleInvariantSelector act S
  class_inhabited_nonvacuous : Nonempty X →
    ∃ (S : ℝ → X → Prop) (f : X → ℝ) (x₀ : X),
      IsJointScaleInvariantSelector act S ∧ IsScaleInvariant act f ∧
        0 < f x₀ ∧ S (f x₀) x₀

theorem scaleHomogeneityNoGoCert (act : ScaleAction X) :
    ScaleHomogeneityNoGoCert X act where
  class_wall := fun S hS f hf x₀ hpos h₀ =>
    no_scaleInvariantSelector_forces_value act S hS f hf x₀ hpos h₀
  admission_export := fun S f hf x₀ hpos h₀ hforces =>
    forcingSelector_not_jointScaleInvariant act S f hf x₀ hpos h₀ hforces
  class_nonempty := ⟨PositivitySelector, positivitySelector_jointScaleInvariant act⟩
  class_inhabited_nonvacuous := fun ⟨x₀⟩ =>
    ⟨PositivitySelector, fun _ => 1, x₀,
      positivitySelector_jointScaleInvariant act,
      fun _c _hc _x => rfl, one_pos, one_pos⟩

/-! ## Witness 1: real pairs with the squared ratio -/

/-- Componentwise scaling of real pairs. -/
def pairScaleAction : ScaleAction (ℝ × ℝ) where
  scale c p := (c * p.1, c * p.2)
  scale_one _ := by ext <;> simp
  scale_mul _ _ _ := by ext <;> simp [mul_assoc]

/-- The squared first-component share: invariant under joint scaling. -/
def pairRatio (p : ℝ × ℝ) : ℝ := p.1 ^ 2 / (p.1 ^ 2 + p.2 ^ 2)

theorem pairRatio_scaleInvariant : IsScaleInvariant pairScaleAction pairRatio := by
  intro c hc p
  show (c * p.1) ^ 2 / ((c * p.1) ^ 2 + (c * p.2) ^ 2) = _
  rw [show (c * p.1) ^ 2 + (c * p.2) ^ 2 = c ^ 2 * (p.1 ^ 2 + p.2 ^ 2) by ring,
    show (c * p.1) ^ 2 = c ^ 2 * p.1 ^ 2 by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (ne_of_gt hc))

/-- The no-go instantiated on real pairs: no scale-blind criterion can
recover the squared ratio as an absolute posted value. -/
theorem pair_witness :
    ¬ ∀ (a : ℝ) (p : ℝ × ℝ), PositivitySelector a p → a = pairRatio p := by
  have hpos : 0 < pairRatio (1, 1) := by norm_num [pairRatio]
  exact no_scaleInvariantSelector_forces_value pairScaleAction _
    (positivitySelector_jointScaleInvariant pairScaleAction)
    pairRatio pairRatio_scaleInvariant _ hpos hpos

/-! ## Witness 2: eight-component complex vectors with a probability weight -/

/-- Pointwise complex scaling of eight-component vectors. -/
def vecScaleAction : ScaleAction (Fin 8 → ℂ) where
  scale c ψ := fun i => (c : ℂ) * ψ i
  scale_one _ := by funext i; simp
  scale_mul _ _ _ := by funext i; push_cast; ring

/-- The probability weight of the first component: invariant under joint
scaling. -/
def probWeight (ψ : Fin 8 → ℂ) : ℝ :=
  ‖ψ 0‖ ^ 2 / ∑ i : Fin 8, ‖ψ i‖ ^ 2

theorem probWeight_scaleInvariant : IsScaleInvariant vecScaleAction probWeight := by
  intro c hc ψ
  have hn : ∀ i : Fin 8, ‖(c : ℂ) * ψ i‖ = c * ‖ψ i‖ := fun i => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  show ‖(c : ℂ) * ψ 0‖ ^ 2 / (∑ i : Fin 8, ‖(c : ℂ) * ψ i‖ ^ 2) = _
  rw [show (∑ i : Fin 8, ‖(c : ℂ) * ψ i‖ ^ 2) = c ^ 2 * ∑ i : Fin 8, ‖ψ i‖ ^ 2 by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hn i]; ring]
  rw [show ‖(c : ℂ) * ψ 0‖ ^ 2 = c ^ 2 * ‖ψ 0‖ ^ 2 by rw [hn 0]; ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (ne_of_gt hc))

/-- The no-go instantiated on eight-component complex vectors: no scale-blind
criterion can recover an absolute normalization from a probability
profile. -/
theorem vec_witness :
    ¬ ∀ (a : ℝ) (ψ : Fin 8 → ℂ), PositivitySelector a ψ → a = probWeight ψ := by
  have hpos : 0 < probWeight (fun _ => (1 : ℂ)) := by
    simp only [probWeight, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    norm_num
  exact no_scaleInvariantSelector_forces_value vecScaleAction _
    (positivitySelector_jointScaleInvariant vecScaleAction)
    probWeight probWeight_scaleInvariant _ hpos hpos

end

/-! ## The amplitude form (the paper's S5 statement)

The capstone paper states the no-go in amplitude form: a scaled
configuration space is a type carrying an action of the multiplicative
group of positive reals and a degree-one homogeneous amplitude readout,
and an invariant selector is a predicate blind to the action. The
selected amplitude set is then either contained in `0` or contains every
positive real, so no positive amplitude is forced unless the selector is
unsatisfiable. The witness is the positive quadrant with `A(a,b) = a`
and the selector `a = 2b`, which pins the scale-invariant ratio `a/b`
to `2` while leaving the amplitude completely free: dimensionless
readouts are outside the theorem's reach. This section is that form,
kernel-checked, with its witness. -/

namespace AmplitudeForm

/-- A scaled configuration space: a carrier with a multiplicative
`ℝ_{>0}`-action and a nonnegative amplitude readout, homogeneous of
degree one. -/
structure ScaledConfigSpace where
  X : Type u
  scale : {c : ℝ // 0 < c} → X → X
  scale_one : ∀ x, scale ⟨1, one_pos⟩ x = x
  scale_mul : ∀ (c d : {c : ℝ // 0 < c}) (x : X),
    scale ⟨c.1 * d.1, mul_pos c.2 d.2⟩ x = scale c (scale d x)
  A : X → ℝ
  A_nonneg : ∀ x, 0 ≤ A x
  A_homog : ∀ (c : {c : ℝ // 0 < c}) (x : X), A (scale c x) = c.1 * A x

namespace ScaledConfigSpace

variable (sp : ScaledConfigSpace)

/-- A selector is invariant when it cannot distinguish a configuration
from its rescaled copy. -/
def IsInvariantSelector (P : sp.X → Prop) : Prop :=
  ∀ (c : {c : ℝ // 0 < c}) (x : sp.X), P (sp.scale c x) ↔ P x

/-- The scale-homogeneity no-go, amplitude form: the selected amplitude
set is either contained in `{0}` or contains every positive real. -/
theorem selected_amplitudes_eq_zero_or_all_pos
    (P : sp.X → Prop) (hP : IsInvariantSelector sp P) :
    (∀ x, P x → sp.A x = 0) ∨ (∀ c : ℝ, 0 < c → ∃ x, P x ∧ sp.A x = c) := by
  by_cases h : ∃ x, P x ∧ 0 < sp.A x
  · right
    obtain ⟨x, hx, hA⟩ := h
    intro c hc
    refine ⟨sp.scale ⟨c / sp.A x, div_pos hc hA⟩ x, ?_, ?_⟩
    · exact (hP _ x).mpr hx
    · rw [sp.A_homog, div_mul_cancel₀ c (ne_of_gt hA)]
  · left
    intro x hx
    have h1 : sp.A x ≤ 0 := by
      by_contra hgt
      push_neg at hgt
      exact h ⟨x, hx, hgt⟩
    exact le_antisymm h1 (sp.A_nonneg x)

/-- Consequence: an invariant selector that is satisfied somewhere
cannot force every selected configuration to have one positive
amplitude. -/
theorem no_forced_positive_amplitude
    (P : sp.X → Prop) (hP : IsInvariantSelector sp P)
    (a : ℝ) (ha : 0 < a) :
    (∃ x, P x) → ¬ ∀ x, P x → sp.A x = a := by
  intro ⟨x0, hx0⟩ hall
  rcases selected_amplitudes_eq_zero_or_all_pos sp P hP with hz | hallpos
  · have h0 := hz x0 hx0
    rw [hall x0 hx0] at h0
    linarith
  · obtain ⟨y, hy, hAy⟩ := hallpos (2 * a) (by linarith)
    have := hall y hy
    linarith

end ScaledConfigSpace

/-- The positive quadrant as a scaled configuration space, with the
first coordinate as amplitude. -/
def quadrantSpace : ScaledConfigSpace where
  X := { p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 }
  scale := fun c p => ⟨(c.1 * p.1.1, c.1 * p.1.2),
    mul_pos c.2 p.2.1, mul_pos c.2 p.2.2⟩
  scale_one := fun p => by ext <;> simp
  scale_mul := fun c d p => by ext <;> simp [mul_assoc]
  A := fun p => p.1.1
  A_nonneg := fun p => le_of_lt p.2.1
  A_homog := fun c p => rfl

/-- The paper's witness selector: `a = 2b`. -/
def quadrantSelector : quadrantSpace.X → Prop := fun p => p.1.1 = 2 * p.1.2

theorem quadrantSelector_invariant :
    quadrantSpace.IsInvariantSelector quadrantSelector := by
  intro c p
  show (c.1 * p.1.1 = 2 * (c.1 * p.1.2)) ↔ (p.1.1 = 2 * p.1.2)
  constructor
  · intro h
    have hc : c.1 ≠ 0 := ne_of_gt c.2
    have h3 : c.1 * (p.1.1 - 2 * p.1.2) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h3 with hc0 | hdiff
    · exact absurd hc0 hc
    · linarith
  · intro h
    rw [h]; ring

/-- The witness point (2, 1) in the positive quadrant. -/
def quadrantPoint21 : quadrantSpace.X :=
  ⟨(2, 1), by norm_num, by norm_num⟩

theorem quadrantPoint21_selected : quadrantSelector quadrantPoint21 := by
  show (2 : ℝ) = 2 * 1
  norm_num

theorem quadrantPoint21_amplitude : quadrantSpace.A quadrantPoint21 = 2 := rfl

theorem quadrant_witness :
    (∃ x, quadrantSelector x ∧ 0 < quadrantSpace.A x) ∧
    ¬ ∀ x, quadrantSelector x → quadrantSpace.A x = 2 := by
  refine ⟨⟨quadrantPoint21, quadrantPoint21_selected, ?_⟩, ?_⟩
  · rw [quadrantPoint21_amplitude]; norm_num
  · exact quadrantSpace.no_forced_positive_amplitude _
      quadrantSelector_invariant 2 (by norm_num)
      ⟨quadrantPoint21, quadrantPoint21_selected⟩

/-- The scale-invariant readout `B(a,b) = a/b`: constant on orbits, and
pinned to `2` on every selected configuration. This is the content of
the paper's "what this theorem does not add" remark, kernel-checked. -/
theorem quadrant_ratio_pinned (p : quadrantSpace.X)
    (hp : quadrantSelector p) : p.1.1 / p.1.2 = 2 := by
  have hb : p.1.2 ≠ 0 := ne_of_gt p.2.2
  have hp' : p.1.1 = 2 * p.1.2 := hp
  field_simp
  linarith

theorem quadrant_ratio_scaleInvariant (c : {c : ℝ // 0 < c})
    (p : quadrantSpace.X) :
    (quadrantSpace.scale c p).1.1 / (quadrantSpace.scale c p).1.2 =
      p.1.1 / p.1.2 := by
  show (c.1 * p.1.1) / (c.1 * p.1.2) = p.1.1 / p.1.2
  exact mul_div_mul_left _ _ (ne_of_gt c.2)

end AmplitudeForm

end ScaleHomogeneityNoGo
end Foundation
end IndisputableMonolith
