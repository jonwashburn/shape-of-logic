import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace LightCone

variable {α : Type}

-- Minimal local Kinematics/ReachN for WIP to avoid external dependency
namespace Local
structure Kinematics (α : Type) where
  step : α → α → Prop
inductive ReachN {α} (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z
end Local

structure StepBounds (K : Local.Kinematics α)
    (U : IndisputableMonolith.Constants.RSUnits)
    (time rad : α → ℝ) : Prop where
  step_time : ∀ {y z}, K.step y z → time z = time y + U.tau0
  step_rad  : ∀ {y z}, K.step y z → rad z ≤ rad y + U.ell0

namespace StepBounds

variable {K : Local.Kinematics α}
variable {U : IndisputableMonolith.Constants.RSUnits}
variable {time rad : α → ℝ}

lemma reach_time_eq
  (H : StepBounds K U time rad) :
  ∀ {n x y}, Local.ReachN K n x y → time y = time x + (n : ℝ) * U.tau0 := by
  intro n x y h
  induction h with
  | zero => simp
  | @succ n x y z hxy hyz ih =>
      have ht := H.step_time hyz
      calc
        time z = time y + U.tau0 := ht
        _ = (time x + (n : ℝ) * U.tau0) + U.tau0 := by simpa [ih]
        _ = time x + ((n : ℝ) * U.tau0 + U.tau0) := by simp [add_comm, add_left_comm, add_assoc]
        _ = time x + (((n : ℝ) + 1) * U.tau0) := by
              have : (n : ℝ) * U.tau0 + U.tau0 = ((n : ℝ) + 1) * U.tau0 := by
                calc
                  (n : ℝ) * U.tau0 + U.tau0
                      = (n : ℝ) * U.tau0 + 1 * U.tau0 := by simpa [one_mul]
                  _ = ((n : ℝ) + 1) * U.tau0 := by simpa [add_mul, one_mul]
              simp [this]
        _ = time x + ((Nat.succ n : ℝ) * U.tau0) := by
              simpa [Nat.cast_add, Nat.cast_one]

lemma reach_rad_le
  (H : StepBounds K U time rad) :
  ∀ {n x y}, Local.ReachN K n x y → rad y ≤ rad x + (n : ℝ) * U.ell0 := by
  intro n x y h
  induction h with
  | zero => simp
  | @succ n x y z hxy hyz ih =>
      have hr := H.step_rad hyz
      calc
        rad z ≤ rad y + U.ell0 := hr
        _ ≤ (rad x + (n : ℝ) * U.ell0) + U.ell0 := by
              simpa using (add_le_add_left ih U.ell0)
        _ = rad x + ((n : ℝ) * U.ell0 + U.ell0) := by simp [add_comm, add_left_comm, add_assoc]
        _ = rad x + (((n : ℝ) + 1) * U.ell0) := by
              have : (n : ℝ) * U.ell0 + U.ell0 = ((n : ℝ) + 1) * U.ell0 := by
                calc
                  (n : ℝ) * U.ell0 + U.ell0
                      = (n : ℝ) * U.ell0 + 1 * U.ell0 := by simpa [one_mul]
                  _ = ((n : ℝ) + 1) * U.ell0 := by simpa [add_mul, one_mul]
              simp [this]
        _ = rad x + ((Nat.succ n : ℝ) * U.ell0) := by
              simpa [Nat.cast_add, Nat.cast_one]

lemma cone_bound
  (H : StepBounds K U time rad)
  {n x y} (h : Local.ReachN K n x y) :
  rad y - rad x ≤ U.c * (time y - time x) := by
  have ht := H.reach_time_eq (K:=K) (U:=U) (time:=time) (rad:=rad) h
  have hr := H.reach_rad_le  (K:=K) (U:=U) (time:=time) (rad:=rad) h
  have hτ : time y - time x = (n : ℝ) * U.tau0 := by
    have := congrArg (fun t => t - time x) ht
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hℓ : rad y - rad x ≤ (n : ℝ) * U.ell0 := by
    have := hr
    -- rearrange ≤ to a difference inequality
    have := sub_le_iff_le_add'.mpr this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  -- In minimal RSUnits, ell0 = c * tau0 is available as the supplied field
  have hcτ : U.ell0 = U.c * U.tau0 := by simpa using (U.c_ell0_tau0).symm
  simpa [hτ, hcτ, mul_left_comm, mul_assoc] using hℓ

/-- Saturation lemma restated: equality holds when each step exactly reaches its bounds. -/
lemma cone_bound_saturates
  (H : StepBounds K U time rad)
  (ht : ∀ {y z}, K.step y z → time z = time y + U.tau0)
  (hr : ∀ {y z}, K.step y z → rad z = rad y + U.ell0)
  {n x y} (h : Local.ReachN K n x y) :
  rad y - rad x = U.c * (time y - time x) := by
  have hineq := cone_bound (K:=K) (U:=U) (time:=time) (rad:=rad) H h
  have ht' : time y - time x = (n : ℝ) * U.tau0 := by
    have := H.reach_time_eq (K:=K) (U:=U) (time:=time) (rad:=rad) h
    have := congrArg (fun t => t - time x) this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hr' : rad y - rad x = (n : ℝ) * U.ell0 := by
    induction h with
    | zero => simp
    | @succ n x y z hxy hyz ih =>
        have hineq_y : rad y - rad x ≤ U.c * (time y - time x) := H.cone_bound hxy
        have ht_y : time y - time x = (n : ℝ) * U.tau0 := by
          have := H.reach_time_eq hxy
          have := congrArg (fun t => t - time x) this
          simp [sub_eq_add_neg, add_comm, add_left_comm] at this
          exact this
        have ih_applied := ih hineq_y ht_y
        have hz := hr hyz
        calc
          rad z - rad x = (rad y + U.ell0) - rad x := by rw [hz]
          _ = (rad y - rad x) + U.ell0 := by ring
          _ = (n : ℝ) * U.ell0 + U.ell0 := by rw [ih_applied]
          _ = ((n : ℝ) + 1) * U.ell0 := by ring
          _ = ((Nat.succ n : ℝ)) * U.ell0 := by simp [Nat.cast_add, Nat.cast_one]
  have hcτ : U.ell0 = U.c * U.tau0 := by simpa using (U.c_ell0_tau0).symm
  calc
    rad y - rad x = (n : ℝ) * U.ell0 := hr'
    _ = (n : ℝ) * (U.c * U.tau0) := by rw [hcτ]
    _ = U.c * ((n : ℝ) * U.tau0) := by ring
    _ = U.c * (time y - time x) := by rw [ht']

end StepBounds
end LightCone
end IndisputableMonolith
