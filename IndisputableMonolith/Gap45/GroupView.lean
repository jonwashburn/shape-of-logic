import Mathlib

namespace IndisputableMonolith
namespace Gap45
namespace GroupView

open Nat

/-- If an element `g` has both 8‑power and 45‑power equal to identity in a group,
its order divides `gcd(8,45)=1`, hence `g = 1`. -/
lemma trivial_intersection_pow {G : Type*} [Group G] {g : G}
  (h8 : g ^ 8 = 1) (h45 : g ^ 45 = 1) : g = 1 := by
  have h8d : orderOf g ∣ 8 := orderOf_dvd_of_pow_eq_one h8
  have h45d : orderOf g ∣ 45 := orderOf_dvd_of_pow_eq_one h45
  have hgcd : orderOf g ∣ Nat.gcd 8 45 := Nat.dvd_gcd h8d h45d
  have hone : orderOf g ∣ 1 := by simpa using hgcd
  have h1 : orderOf g = 1 := Nat.dvd_one.mp hone
  exact (orderOf_eq_one_iff.mp h1)

end GroupView
end Gap45
end IndisputableMonolith
