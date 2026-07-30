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

end ScaleHomogeneityNoGo
end Foundation
end IndisputableMonolith
