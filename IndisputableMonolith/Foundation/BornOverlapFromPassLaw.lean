import Mathlib
import IndisputableMonolith.Foundation.BornLawFromThePass

/-!
# The Born overlap is what a pass law counts

The pass law is stated over real inner product spaces: a count is nonnegative,
every unit state counts one, and orthogonal parts of one pass count separately
as they count together. Those three conditions force the count of a part to be
the square of its length.

Recognition records carry amplitude and phase, so the space a recognition
compares in is complex, and the quantity a comparison returns is the squared
overlap. This module carries the pass law across that gap. A complex inner
product space is a real one for the same norm, so a pass law on it is a pass law
in the sense already proved; the part that one unit state selects from another is
the component along its complex line; and the squared length of that component is
exactly the squared overlap.

The consequence is that the squared-overlap form of comparison does not have to
be adopted. It is what any count satisfying the three pass conditions must be.
Nothing here assumes a comparison is a squared modulus, and nothing here uses a
frame-function theorem.

Scope: the count is the one a pass law assigns; whether a physical comparison
obeys the three pass conditions is the premise this module carries, and it is
strictly weaker than assuming the squared-overlap form. Wiring this to the
eight-tick register as coordinatized elsewhere in the library, which carries its
own hand-rolled squared modulus rather than the Mathlib inner product norm, is a
separate mechanical step and is not done here.
-/

namespace IndisputableMonolith
namespace Foundation
namespace BornOverlapFromPassLaw

open BornLawFromThePass

noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The part of `φ` that the unit state `ψ` selects: the component of `φ` along
the complex line through `ψ`. -/
def selected (ψ φ : E) : E := (inner ℂ ψ φ : ℂ) • ψ

/-- The selected part has length exactly the modulus of the overlap. -/
theorem norm_selected (ψ φ : E) (hψ : ‖ψ‖ = 1) :
    ‖selected ψ φ‖ = ‖(inner ℂ ψ φ : ℂ)‖ := by
  rw [selected, norm_smul, hψ, mul_one]

/-- The selected part fits inside one pass. -/
theorem norm_selected_le_one (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ ≤ 1) :
    ‖selected ψ φ‖ ≤ 1 := by
  rw [norm_selected ψ φ hψ]
  have hCS : ‖(inner ℂ ψ φ : ℂ)‖ ≤ ‖ψ‖ * ‖φ‖ := norm_inner_le_norm ψ φ
  rw [hψ, one_mul] at hCS
  exact le_trans hCS hφ

/-- **The Born overlap is what a pass law counts.** On a complex inner product
space of three or more real directions, any count satisfying the three pass
conditions assigns to the part that one unit state selects from another exactly
the squared modulus of their overlap. The squared-overlap form of comparison is
therefore forced, not adopted. -/
theorem count_selected_eq_born
    [FiniteDimensional ℝ E]
    (L : PassLaw E) (hrank : 3 ≤ Module.finrank ℝ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ ≤ 1) :
    L.count (selected ψ φ) = ‖(inner ℂ ψ φ : ℂ)‖ ^ 2 := by
  rw [L.count_eq_sq_norm hrank (selected ψ φ) (norm_selected_le_one ψ φ hψ hφ),
    norm_selected ψ φ hψ]

/-- Two pass laws on a complex space agree on every comparison, so the
comparison rule is unique as well as forced. -/
theorem born_comparison_unique
    [FiniteDimensional ℝ E]
    (L L' : PassLaw E) (hrank : 3 ≤ Module.finrank ℝ E)
    (ψ φ : E) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ ≤ 1) :
    L.count (selected ψ φ) = L'.count (selected ψ φ) := by
  rw [count_selected_eq_born L hrank ψ φ hψ hφ,
    count_selected_eq_born L' hrank ψ φ hψ hφ]

/-- Self-comparison of a unit state counts one: the pass is complete. -/
theorem count_selected_self
    [FiniteDimensional ℝ E]
    (L : PassLaw E) (hrank : 3 ≤ Module.finrank ℝ E)
    (ψ : E) (hψ : ‖ψ‖ = 1) :
    L.count (selected ψ ψ) = 1 := by
  rw [count_selected_eq_born L hrank ψ ψ hψ (le_of_eq hψ)]
  have hself : (inner ℂ ψ ψ : ℂ) = ((‖ψ‖ : ℝ) : ℂ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hself, hψ]
  norm_num

/-! ## The premise class is inhabited, and it discriminates

A forcing theorem over an empty hypothesis class proves nothing, and a forcing
theorem that cannot reject the obvious alternative has not been tested. Both are
answered here.
-/

/-- **The hypothesis class is inhabited on a complex space.** The count that
squares the length satisfies the three pass conditions, so the forcing theorem
above is not vacuous. -/
theorem passLaw_inhabited_complex : Nonempty (PassLaw E) :=
  ⟨bornPassLaw E⟩

/-- The exhibited law does return the Born overlap on the selected part. -/
theorem bornPassLaw_selected (ψ φ : E) (hψ : ‖ψ‖ = 1) :
    (bornPassLaw E).count (selected ψ φ) = ‖(inner ℂ ψ φ : ℂ)‖ ^ 2 := by
  rw [bornPassLaw_count, norm_selected ψ φ hψ]

/-- **Why the square, and not the modulus.** No law of recognition makes the
comparison of two states the bare modulus of their overlap. The witness is a
state compared against half of itself: the pass conditions force a quarter, and
the modulus rule claims a half. This is the alternative a reader reaches for
first, and it is excluded rather than merely not chosen. -/
theorem no_modulus_comparison_law
    [FiniteDimensional ℝ E]
    (hrank : 3 ≤ Module.finrank ℝ E) (ψ : E) (hψ : ‖ψ‖ = 1) :
    ¬ ∃ L : PassLaw E, ∀ φ : E, ‖φ‖ ≤ 1 →
        L.count (selected ψ φ) = ‖(inner ℂ ψ φ : ℂ)‖ := by
  rintro ⟨L, hL⟩
  have hself : (inner ℂ ψ ψ : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_cast
  have hinner : (inner ℂ ψ ((1/2 : ℂ) • ψ) : ℂ) = 1/2 := by
    rw [inner_smul_right, hself, mul_one]
  have hnormhalf : ‖(inner ℂ ψ ((1/2 : ℂ) • ψ) : ℂ)‖ = 1/2 := by
    rw [hinner]
    norm_num
  have hφ : ‖(1/2 : ℂ) • ψ‖ ≤ 1 := by
    rw [norm_smul, hψ, mul_one]
    norm_num
  have hclaim := hL ((1/2 : ℂ) • ψ) hφ
  have hforced := count_selected_eq_born L hrank ψ ((1/2 : ℂ) • ψ) hψ hφ
  rw [hclaim, hnormhalf] at hforced
  norm_num at hforced

/-! ## The eight-tick register

The register a recognition cycle writes into is eight complex amplitudes with
the squared-modulus norm, which is `EuclideanSpace ℂ (Fin 8)`. Its real
dimension is sixteen, so the three-direction requirement is met with room, and
the forced comparison rule applies to it.
-/

/-- The register has sixteen real directions, hence far more than three. -/
theorem three_le_finrank_register :
    3 ≤ Module.finrank ℝ (EuclideanSpace ℂ (Fin 8)) := by
  have htower : Module.finrank ℝ ℂ * Module.finrank ℂ (EuclideanSpace ℂ (Fin 8))
      = Module.finrank ℝ (EuclideanSpace ℂ (Fin 8)) :=
    Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin 8))
  have hC : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have hreg : Module.finrank ℂ (EuclideanSpace ℂ (Fin 8)) = 8 := by
    simp
  rw [hC, hreg] at htower
  omega

/-- **The comparison rule on the eight-tick register is the Born overlap.** -/
theorem register_comparison_is_born
    (L : PassLaw (EuclideanSpace ℂ (Fin 8)))
    (ψ φ : EuclideanSpace ℂ (Fin 8)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ ≤ 1) :
    L.count (selected ψ φ) = ‖(inner ℂ ψ φ : ℂ)‖ ^ 2 :=
  count_selected_eq_born L three_le_finrank_register ψ φ hψ hφ

end

end BornOverlapFromPassLaw
end Foundation
end IndisputableMonolith
