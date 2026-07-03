import Mathlib.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# RRF Core: Display Channel

A display channel is a way of "observing" or "projecting" a state into an observation space.
-/

namespace IndisputableMonolith
namespace RRF.Core

/-- A display channel from State to Observation. -/
structure DisplayChannel (State Obs : Type*) where
  observe : State → Obs
  quality : Obs → ℝ

namespace DisplayChannel

variable {State Obs : Type*}

/-- The composed quality function: State → ℝ. -/
def stateQuality (C : DisplayChannel State Obs) : State → ℝ :=
  C.quality ∘ C.observe

/-- A state is optimal in channel C if it minimizes quality. -/
def isOptimal (C : DisplayChannel State Obs) (x : State) : Prop :=
  ∀ y, C.stateQuality x ≤ C.stateQuality y

end DisplayChannel

/-- A collection of display channels on the same state space. -/
structure ChannelBundle (State : Type*) where
  Index : Type*
  Obs : Index → Type*
  channel : (i : Index) → DisplayChannel State (Obs i)

namespace ChannelBundle

variable {State : Type*}

def isGloballyOptimal (B : ChannelBundle State) (x : State) : Prop :=
  ∀ i, (B.channel i).isOptimal x

end ChannelBundle

/-- Two channels are quality-equivalent if they induce the same ordering on states. -/
abbrev QualityEquiv {State Obs₁ Obs₂ : Type*}
    (C₁ : DisplayChannel State Obs₁)
    (C₂ : DisplayChannel State Obs₂) : Prop :=
  ∀ x y : State, C₁.stateQuality x ≤ C₁.stateQuality y ↔
                  C₂.stateQuality x ≤ C₂.stateQuality y

namespace QualityEquiv

variable {State Obs₁ Obs₂ Obs₃ : Type*}

theorem refl (C : DisplayChannel State Obs₁) : QualityEquiv C C :=
  fun _ _ => Iff.rfl

theorem symm {C₁ : DisplayChannel State Obs₁} {C₂ : DisplayChannel State Obs₂}
    (h : QualityEquiv C₁ C₂) : QualityEquiv C₂ C₁ :=
  fun x y => (h x y).symm

theorem trans {C₁ : DisplayChannel State Obs₁}
    {C₂ : DisplayChannel State Obs₂}
    {C₃ : DisplayChannel State Obs₃}
    (h₁₂ : QualityEquiv C₁ C₂) (h₂₃ : QualityEquiv C₂ C₃) : QualityEquiv C₁ C₃ :=
  fun x y => (h₁₂ x y).trans (h₂₃ x y)

/-- Quality-equivalent channels have the same optimal states. -/
theorem optimal_iff {C₁ : DisplayChannel State Obs₁} {C₂ : DisplayChannel State Obs₂}
    (heq : QualityEquiv C₁ C₂) (x : State) :
    C₁.isOptimal x ↔ C₂.isOptimal x :=
  ⟨fun h1 y => (heq x y).mp (h1 y), fun h2 y => (heq x y).mpr (h2 y)⟩

end QualityEquiv

end RRF.Core
end IndisputableMonolith
