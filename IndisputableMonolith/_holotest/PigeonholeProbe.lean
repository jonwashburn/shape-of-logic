import Mathlib

namespace HoloTest

theorem pigeonhole_fin9_fin8 (f : Fin 9 → Fin 8) :
    ∃ i j : Fin 9, i ≠ j ∧ f i = f j :=
  Fintype.exists_ne_map_eq_of_card_lt f (by decide)

end HoloTest
