/-
  PrimitiveRecognitionCalculus/PRCModelTheoryNonForcing.lean

  Round-trip source:
    δ/Delta_Continuum_Is_Not_Forced.tex  (the model-theory / definability
    non-forcing argument, the fourth of the paper's four independent
    arguments that the continuum is not forced).

  This module formalizes that fourth argument. The paper gives four
  independent routes to "distinction does not force the continuum":

    1. cardinality              (real_not_countable, etc.)
    2. generative countability  (generated_countable, in PRCNativeCostUniqueness)
    3. measure zero             (generated_volume_zero, in PRCNativeCostUniqueness)
    4. model theory             (this file)

  The model-theory route is the sharpest: it says no *first-order* description
  in a countable language can pin ℝ down to isomorphism, because downward
  Löwenheim–Skolem produces a countable structure that satisfies exactly the
  same first-order sentences as ℝ yet cannot be isomorphic to it (it has the
  wrong cardinality). Whatever first-order theory distinction writes about its
  number line, a countable companion validates every sentence of it.

  We isolate the heavy `Mathlib.ModelTheory` import in this sibling module so
  the rest of the PRC cost-uniqueness development does not pay the build cost.
-/

import Mathlib.ModelTheory.Satisfiability
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ModelTheoryNonForcing

open Cardinal FirstOrder

/-- **Downward Löwenheim–Skolem for the reals.**
For any countable first-order language `L` in which `ℝ` carries a structure,
there is a *countable* `L`-structure `N` that is elementarily equivalent to
`ℝ` (i.e. `ℝ ≅[L] N`): `N` satisfies exactly the same `L`-sentences as `ℝ`.

This is the engine of the model-theory non-forcing argument. The hypothesis
`hL : L.card ≤ ℵ₀` is the "countable language" assumption: distinction can
only write down countably many primitive relations, functions, and constants. -/
theorem real_has_countable_ee_model
    {L : FirstOrder.Language.{0, 0}} [L.Structure ℝ] (hL : L.card ≤ Cardinal.aleph0) :
    ∃ N : CategoryTheory.Bundled L.Structure, (ℝ ≅[L] N) ∧ Cardinal.mk N = Cardinal.aleph0 :=
  FirstOrder.Language.exists_elementarilyEquivalent_card_eq L ℝ Cardinal.aleph0
    le_rfl (by simpa using hL)

/-- **The reals are not first-order categorical (in any countable language).**
For any countable language structure on `ℝ`, there is a structure `N`
elementarily equivalent to `ℝ` that is *not* isomorphic to `ℝ` even as a bare
type: it is countable while `ℝ` has cardinality continuum.

Consequence for the δ program: no first-order description in a countable
language fixes `ℝ` up to isomorphism. Distinction may force a complete
first-order theory of its number line, and `ℝ` may be one model of it, but a
countable model of the very same theory always exists. The continuum is not
forced by any amount of first-order distinction. -/
theorem real_not_first_order_categorical
    {L : FirstOrder.Language.{0, 0}} [L.Structure ℝ] (hL : L.card ≤ Cardinal.aleph0) :
    ∃ N : CategoryTheory.Bundled L.Structure,
      (ℝ ≅[L] N) ∧ Cardinal.mk ℝ ≠ Cardinal.mk N := by
  obtain ⟨N, hee, hcard⟩ := real_has_countable_ee_model hL
  refine ⟨N, hee, ?_⟩
  rw [hcard, Cardinal.mk_real]
  exact Cardinal.aleph0_lt_continuum.ne'

/-- The countable elementarily-equivalent companion exists and is a genuine
witness of non-forcing: it agrees with `ℝ` on every first-order sentence yet
is countable, hence not equinumerous with `ℝ`. Packaged form combining all
three facts for downstream citation. (Equinumerosity is necessary for any
structure isomorphism, so distinct cardinals rule out `ℝ ≃ N` of any kind.) -/
theorem real_first_order_underdetermined
    {L : FirstOrder.Language.{0, 0}} [L.Structure ℝ] (hL : L.card ≤ Cardinal.aleph0) :
    ∃ N : CategoryTheory.Bundled L.Structure,
      (ℝ ≅[L] N) ∧ Cardinal.mk N = Cardinal.aleph0 ∧ Cardinal.mk ℝ ≠ Cardinal.mk N := by
  obtain ⟨N, hee, hcard⟩ := real_has_countable_ee_model hL
  refine ⟨N, hee, hcard, ?_⟩
  rw [hcard, Cardinal.mk_real]
  exact Cardinal.aleph0_lt_continuum.ne'

end ModelTheoryNonForcing
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
