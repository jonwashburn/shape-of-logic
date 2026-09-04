import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Row 2 by cutset: the two kernel cost fields

`RecognitionKernelV2` carries two qualitative fields on the cost `F` beyond the
composition law: `nondegenerate` (the cost tells some two ratios apart) and
`monotone_imbalance` (a larger log-imbalance never costs less). Neither is a
ledger row today; both are sentences of the kernel. This module prices them by
cutset.

## 2a, nondegenerate: derived from T1's own word for cost

The floor's word for a cost is T1's: nonnegative, and zero exactly on the
balanced configuration (`CostFunction.nonneg`, `CostFunction.dichotomy` in
`CostFromDistinction`). Transported to ratios, dichotomy reads `F x = 0 ↔ x = 1`
(`Dichotomy`). Among composition-law solutions the violators of nondegeneracy
are the two constants `0` and `-1` (`normalized_of_nondegenerate` shows the
`-1` branch is the only one besides normalization). Both fail dichotomy; `J`
passes it; and the exclusion is universal (`nondegenerate_of_dichotomy`, no
composition law needed). `row2a` inhabits the harness. The blade is strictly
stronger than the sentence (every gauge member `J(x^c)` passes it), so this is
a cut and not a relabel: `nondegenerate` is not a new sentence, it is T1's
dichotomy read on ratios.

## 2b, monotone: B4 tested and found half-reaching

B4 was to be "finite recognizer: bounded debt capacity; a cost law under which
imbalance is free or rewarded has no finite recognizer surviving it". Its floor
form is T1's other field, nonnegativity: no imbalance is rewarded
(`NoReward`). This module writes the countermodel the plan asked for: the
**cosine cost** `cos (log x) - 1`. It satisfies the composition law
(d'Alembert with cosine), is reciprocal, normalized and nondegenerate, and it
rewards imbalance: at `x = e^π` the cost is `-2`. Its log-profile `cos t` is
not monotone on `[0, ∞)`. So `NoReward` kills the planted negative and `J`
passes it. But `NoReward` does **not** reach `monotone_imbalance`: the
composition law has wild solutions `cosh (a t)` with `a` a discontinuous
additive map, nonnegative and nowhere monotone. Monotonicity in the kernel does
two jobs, (i) no reward and (ii) regularity in place of continuity, and a
floor word about debt covers only (i). The regularity half is the continuum
purchase the ledger already prices (`N-route-fnd-force-T5-from-boolean-floor-
alone`). Row 2b therefore stays a sentence; what changed is that it is now
split into a floor half (T1 nonnegativity) and a priced half (regularity),
with the split witnessed by the cosine cost on one side and by the wild
solutions (classical, not formalized here) on the other. The receipt says so.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row2Cost

open Cost Cost.FunctionalEquation

noncomputable section

/-! ## The kernel fields, named -/

/-- `RecognitionKernelV2.nondegenerate`. -/
def Nondegenerate (F : ℝ → ℝ) : Prop := ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ F x ≠ F y

/-- `RecognitionKernelV2.monotone_imbalance`. -/
def MonotoneImbalance (F : ℝ → ℝ) : Prop := MonotoneOn (H F) (Set.Ici (0 : ℝ))

/-! ## 2a: dichotomy, T1's word for cost, on ratios -/

/-- T1 dichotomy on ratios: the cost vanishes exactly at balance. -/
def Dichotomy (F : ℝ → ℝ) : Prop := ∀ x : ℝ, 0 < x → (F x = 0 ↔ x = 1)

theorem jcost_dichotomy : Dichotomy Jcost := fun x hx => Jcost_eq_zero_iff x hx

theorem jcost_rcl : SatisfiesCompositionLaw Jcost :=
  (composition_law_equiv_coshAdd Jcost).2 Jcost_cosh_add_identity

/-- The constant cost at `v` satisfies the composition law iff `v ∈ {0, -1}`. -/
theorem const_rcl (v : ℝ) (hv : v = 0 ∨ v = -1) : SatisfiesCompositionLaw (fun _ => v) := by
  intro x y _ _
  rcases hv with rfl | rfl <;> norm_num

theorem const_not_nondegenerate (v : ℝ) : ¬ Nondegenerate (fun _ => v) := by
  rintro ⟨x, y, _, _, h⟩
  exact h rfl

/-- **Universal exclusion.** A degenerate cost is constant on the positive axis
and fails dichotomy at `1` or at `2`. -/
theorem nondegenerate_of_dichotomy (F : ℝ → ℝ) (hD : Dichotomy F) : Nondegenerate F := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  intro h
  have h1 : F 1 = 0 := (hD 1 one_pos).2 rfl
  have h2 : F 2 ≠ 0 := fun h0 => by
    have := (hD 2 (by norm_num)).1 h0
    norm_num at this
  exact h2 (h.symm.trans h1)

theorem const_not_dichotomy (v : ℝ) : ¬ Dichotomy (fun _ => v) :=
  fun h => const_not_nondegenerate v (nondegenerate_of_dichotomy _ h)

/-- Every gauge member passes the blade: dichotomy is not `J`'s private
property, so the blade does not smuggle the unit. -/
theorem costLambda_dichotomy (c : ℝ) (hc : 0 < c) :
    Dichotomy (fun x => (x ^ c + x ^ (-c)) / 2 - 1) := by
  intro x hx
  show (x ^ c + x ^ (-c)) / 2 - 1 = 0 ↔ x = 1
  have hpos : 0 < x ^ c := Real.rpow_pos_of_pos hx c
  have hneg : x ^ (-c) = (x ^ c)⁻¹ := Real.rpow_neg (le_of_lt hx) c
  rw [hneg]
  constructor
  · intro h
    have hJ : Jcost (x ^ c) = 0 := by simp only [Jcost]; linarith
    have h1 : x ^ c = 1 := (Jcost_eq_zero_iff _ hpos).1 hJ
    have h1' : (1 : ℝ) ^ c = x ^ c := by rw [Real.one_rpow]; exact h1.symm
    exact (Real.rpow_left_injOn hc.ne' (Set.mem_setOf.2 zero_le_one)
      (Set.mem_setOf.2 hx.le) h1').symm
  · rintro rfl
    norm_num

/-- Row 2a in harness form. Candidates: composition-law solutions. -/
def row2a : CutsetRow (ℝ → ℝ) where
  Floor := SatisfiesCompositionLaw
  Sentence := Nondegenerate
  Blade := Dichotomy
  provenance := .definition "cost (T1): nonnegative, zero exactly at balance"
  real := Jcost
  real_floor := jcost_rcl
  blade_real := jcost_dichotomy
  violator := fun _ => 0
  violator_floor := const_rcl 0 (Or.inl rfl)
  violator_violates := const_not_nondegenerate 0
  blade_kills_violator := const_not_dichotomy 0
  exclusion := fun F _ hs hb => hs (nondegenerate_of_dichotomy F hb)

/-! ## 2b: B4 as a predicate, and the cosine cost -/

/-- B4 at the floor: no imbalance is rewarded (T1 nonnegativity on ratios). -/
def NoReward (F : ℝ → ℝ) : Prop := ∀ x : ℝ, 0 < x → 0 ≤ F x

theorem jcost_noReward : NoReward Jcost := fun _ hx => Jcost_nonneg hx

theorem jcost_monotone : MonotoneImbalance Jcost := by
  intro s hs t ht hst
  have hs0 : 0 ≤ s := Set.mem_Ici.1 hs
  have ht0 : 0 ≤ t := Set.mem_Ici.1 ht
  simp only [H, Jcost_G_eq_cosh_sub_one]
  have := Real.cosh_le_cosh.2 (abs_le_abs hst (by linarith))
  linarith

/-- **The cosine cost**: a composition-law solution that rewards imbalance. -/
def cosCost (x : ℝ) : ℝ := Real.cos (Real.log x) - 1

theorem cosCost_rcl : SatisfiesCompositionLaw cosCost := by
  intro x y hx hy
  simp only [cosCost, Real.log_mul hx.ne' hy.ne', Real.log_div hx.ne' hy.ne',
    Real.cos_add, Real.cos_sub]
  ring

theorem cosCost_H (t : ℝ) : H cosCost t = Real.cos t := by
  simp [H, G, cosCost, Real.log_exp]

theorem cosCost_normalized : IsNormalized cosCost := by
  simp [IsNormalized, cosCost]

theorem cosCost_reciprocal : IsReciprocalCost cosCost := by
  intro x hx
  simp [cosCost, Real.log_inv, Real.cos_neg]

/-- At `x = e^π` the cosine cost is `-2`: imbalance is rewarded. -/
theorem cosCost_rewards : cosCost (Real.exp Real.pi) = -2 := by
  rw [cosCost, Real.log_exp, Real.cos_pi]
  norm_num

theorem cosCost_one : cosCost 1 = 0 := cosCost_normalized

theorem cosCost_nondegenerate : Nondegenerate cosCost :=
  ⟨1, Real.exp Real.pi, one_pos, Real.exp_pos _, by
    rw [cosCost_rewards, cosCost_one]; norm_num⟩

theorem cosCost_not_noReward : ¬ NoReward cosCost := by
  intro h
  have := h (Real.exp Real.pi) (Real.exp_pos _)
  rw [cosCost_rewards] at this
  linarith

theorem cosCost_not_monotone : ¬ MonotoneImbalance cosCost := by
  intro h
  have := h (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 Real.pi_pos.le) Real.pi_pos.le
  rw [cosCost_H, cosCost_H, Real.cos_zero, Real.cos_pi] at this
  linarith

/-- Nonnegativity is a consequence of monotonicity for normalized costs: the
floor half of `monotone_imbalance`, read off. -/
theorem noReward_of_monotone (F : ℝ → ℝ) (hN : IsNormalized F) (hR : IsReciprocalCost F)
    (hM : MonotoneImbalance F) : NoReward F := by
  intro x hx
  have hN' : F 1 = 0 := hN
  have h0 : H F 0 = 1 := by simp [H, G, hN']
  have key : ∀ t : ℝ, 0 ≤ t → 0 ≤ F (Real.exp t) := by
    intro t ht
    have := hM (Set.mem_Ici.2 (le_refl (0 : ℝ))) (Set.mem_Ici.2 ht) ht
    rw [h0] at this
    simp only [H, G] at this
    linarith
  rcases le_or_gt 0 (Real.log x) with hl | hl
  · have := key _ hl
    rwa [Real.exp_log hx] at this
  · have := key _ (neg_nonneg.2 hl.le)
    rw [Real.exp_neg, Real.exp_log hx] at this
    rwa [hR x hx]

/-! ## Certificate -/

/-- Row 2 certificate: the composition law with the dichotomy blade forces a
normalized reciprocal cost; the cosine cost is a lawful decoy that rewards some
ratio and is not monotone; `J` passes both qualitative tests. -/
structure Cert : Prop where
  row2a_forces : ∀ F, row2a.Floor F → row2a.Blade F → row2a.Sentence F
  row2a_class_nonempty : ∃ F, row2a.Floor F ∧ ¬ row2a.Sentence F
  blade_not_private : ∀ c : ℝ, 0 < c → Dichotomy (fun x => (x ^ c + x ^ (-c)) / 2 - 1)
  cos_is_solution : SatisfiesCompositionLaw cosCost ∧ IsNormalized cosCost ∧
    IsReciprocalCost cosCost ∧ Nondegenerate cosCost
  cos_rewards : ¬ NoReward cosCost
  cos_not_monotone : ¬ MonotoneImbalance cosCost
  j_passes : NoReward Jcost ∧ MonotoneImbalance Jcost
  floor_half : ∀ F, IsNormalized F → IsReciprocalCost F → MonotoneImbalance F → NoReward F

theorem cert : Cert where
  row2a_forces := row2a.forces
  row2a_class_nonempty := row2a.class_nonempty
  blade_not_private := costLambda_dichotomy
  cos_is_solution := ⟨cosCost_rcl, cosCost_normalized, cosCost_reciprocal, cosCost_nondegenerate⟩
  cos_rewards := cosCost_not_noReward
  cos_not_monotone := cosCost_not_monotone
  j_passes := ⟨jcost_noReward, jcost_monotone⟩
  floor_half := noReward_of_monotone

end

end Row2Cost
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
