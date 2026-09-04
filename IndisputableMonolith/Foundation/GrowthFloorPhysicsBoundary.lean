import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost.GeometricRoot
import IndisputableMonolith.Foundation.PhiClosureSelection

/-!
# Growth floor from physics: the boundary, upgraded

Companion to `CostFloorBoundary.lean`, prompted by
`plans/T6_Growth_Floor_From_Physics_Session_Prompt_20260731.txt`: the
what-causes-time chain (`papers/RS_What_Causes_Time_20260731.tex`) carries one
identified physical input, a per-rung ratio floor above the plastic constant
for the ladder of actual posted structure. `CostFloorBoundary.lean` showed the
abstract banked ladder cannot force it. This module asks the follow-up: can
physics *outside* the abstract ladder force it? Two candidate routes were on
the table.

## Route (i): mass-spectrum stability

Survey of what the library banks (read, not guessed): every gap or ratio
structure bottoms out in φ. `Unification/YangMillsMassGap.spectral_gap`
certifies the least nonzero ladder cost `J(φ)`, **on the φ-lattice** — the
rung structure it presumes is what T6 is supposed to derive, so citing it is
circular. `Cosmology/OccupancyDilutionDerived.ladderMinimal_iff_selfSimilar`
proves its "cost floor" premise *equivalent* to the self-recognition closure
`w₁ = 1/(1+w₁)`, the kernel's HYPOTHESIS-tagged step. The mass law's rung
table is integer-valued with the φ-exponent a stated convention
(`Masses/GapFromLedgerCount`). The φ-free reduction of "a stable mass
spectrum" is: per-step costs bounded below by a positive constant, i.e. a
**positive spectral gap**, i.e. some ratio floor `ρ > 1`.

The headline theorem `mass_gap_insufficient_for_recurrence` shows that is not
enough. The plastic ladder (`s n = ρⁿ`, `ρ³ = ρ + 1`, the exact threshold of
`RecurrenceBridge`) has

* a positive spectral gap: every step costs exactly `J(ρ) > 0`,
* adjacent closure (composition lands at rung `n+3`),
* the tick (steps bounded below by `ρ − 1`),
* a ratio floor at `ρ` itself,

and it violates the adjacent recurrence, and **no** floor above the plastic
constant holds for it (`ρ'³ > ρ' + 1` fails for every `ρ'` that floors it).
So "the spectrum has a mass gap" does not force the recurrence. What the
recurrence needs is the gap *above* `J(ρ_plastic)`, and that strict inequality
is not derived from any banked stability physics. Route (i) is dead as a
derivation route in the current library; the input remains exactly "growth
above plastic".

## Route (ii): the eightfold cadence

No banked theorem links the tick period (8 at dimension 3) to rung ratios of
the scale ladder. The tick theorem caps refinement *counts* of a fixed
distinction; rung ratios are free underneath it (that is the content of
`CostFloorBoundary.banked_independence`). Nothing to kernel-check without a
carrier connecting ticks to scale growth, and none exists. Dead without new
physics; recorded in program memory.

## The generation wrinkle, proved

The plastic witness fails the banked ladder's full-generation field:
`plastic_fails_generation_at_two` (rung 2 is not a sum of two smaller rungs).
That failure is not incidental. `uniform_closure_generation_forces_phi`
shows: a *uniform*-ratio ladder with adjacent closure and full generation has
ratio exactly φ, with no floor premise at all (rung-2 generation forces
`r² = 1 + r`, the other pairings contradict closure). So on uniform ladders
the growth floor is free; the floor premise's entire content is non-uniformity.
OPEN (recorded, not attacked here): whether a *non-uniform* ladder with full
generation, a positive spectral gap, closure, and sub-plastic growth exists —
if so, the countermodel upgrades into the full banked-ladder package; if not,
generation is the missing premise in disguise.

No project-local axioms. No sorry.
-/

noncomputable section
namespace IndisputableMonolith
namespace Foundation
namespace GrowthFloorPhysicsBoundary

open Real Constants

/-- **Positive spectral gap (step-cost floor).** A ladder has spectral gap
`c` when every rung step costs at least `c` in J-units: the φ-free reading of
"mass-spectrum stability" (compare `Unification/YangMillsMassGap.spectral_gap`,
which banks `c = J(φ)` on the φ-lattice). -/
def StepCostGap (s : ℕ → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ ∀ n, c ≤ Cost.Jcost (s (n + 1) / s n)

/-- Every step of the plastic ladder has the same ratio, so its spectral gap
is exactly `J(r) > 0`: the witness carries a genuine mass gap. -/
theorem plastic_step_cost_gap {r : ℝ} (hr1 : 1 < r) :
    StepCostGap (fun n => r ^ n) (Cost.Jcost r) := by
  have hr0 : 0 < r := by linarith
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr1).ne'
  have hJ : 0 < Cost.Jcost r := by
    rw [Cost.GeometricRoot.jcost_eq_cosh_log_sub_one hr0]
    linarith [(Real.one_lt_cosh (x := Real.log r)).2 hlog]
  refine ⟨hJ, fun n => ?_⟩
  show Cost.Jcost r ≤ Cost.Jcost (r ^ (n + 1) / r ^ n)
  have hstep : r ^ (n + 1) / r ^ n = r := by
    have hne : r ^ n ≠ 0 := pow_ne_zero n hr0.ne'
    rw [div_eq_iff hne]
    ring
  rw [hstep]

/-- **No floor above plastic holds for the plastic ladder.** Any `ρ' > 1`
flooring it satisfies `ρ' ≤ r` (read off at rung 0), hence
`ρ'³ ≤ ρ' + 1`: the bridge theorem's strict hypothesis fails for every floor
the witness admits. -/
theorem plastic_admits_no_floor_above_plastic {r : ℝ} (hr1 : 1 < r)
    (h13 : 1 + r = r ^ 3) :
    ∀ ρ' : ℝ, 1 < ρ' → (∀ n, ρ' * r ^ n ≤ r ^ (n + 1)) → ρ' ^ 3 ≤ ρ' + 1 := by
  intro ρ' hρ' hfloor
  have hle : ρ' ≤ r := by
    have := hfloor 0
    simpa using this
  have hfac : (0:ℝ) ≤ r ^ 2 + ρ' * r + ρ' ^ 2 - 1 := by nlinarith
  have hprod : (0:ℝ) ≤ (r - ρ') * (r ^ 2 + ρ' * r + ρ' ^ 2 - 1) :=
    mul_nonneg (by linarith) hfac
  have hexp : (r - ρ') * (r ^ 2 + ρ' * r + ρ' ^ 2 - 1) =
      (r ^ 3 - r - 1) - (ρ' ^ 3 - ρ' - 1) := by ring
  rw [hexp] at hprod
  have hr3 : r ^ 3 - r - 1 = 0 := by linarith [h13]
  rw [hr3] at hprod
  linarith [hprod]

/-- The plastic ladder violates the adjacent recurrence at rung 2:
`r² ≠ r + 1 = r³`. -/
theorem plastic_recurrence_violated {r : ℝ} (hr1 : 1 < r)
    (h13 : 1 + r = r ^ 3) :
    ¬ (∀ n : ℕ, r ^ (n + 2) = r ^ (n + 1) + r ^ n) := by
  intro h
  have h0e := h 0
  simp at h0e
  have h2 : r ^ 2 = 1 + r := by linarith [h0e]
  rw [h13] at h2
  have hr0 : 0 < r := by linarith
  have hpos : 0 < r ^ 2 * (r - 1) := mul_pos (by nlinarith) (by linarith)
  have hexp : r ^ 2 * (r - 1) = r ^ 3 - r ^ 2 := by ring
  rw [hexp] at hpos
  have hz : r ^ 3 - r ^ 2 = 0 := by linarith [h2]
  linarith [hpos, hz]

/-- The plastic ladder satisfies the tick: steps never shrink below `r − 1`. -/
theorem plastic_tick {r : ℝ} (hr1 : 1 < r) :
    ∀ n : ℕ, r - 1 ≤ r ^ (n + 1) - r ^ n := by
  intro n
  have h1 : (1:ℝ) ≤ r ^ n := one_le_pow₀ (by linarith)
  have he : r ^ (n + 1) - r ^ n = r ^ n * (r - 1) := by rw [pow_succ']; ring
  rw [he]
  have hle := mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ r - 1)
  linarith [hle]

/-- The plastic ladder has adjacent closure: composition lands at rung
`n + 3` (skipping rung `n + 2`). -/
theorem plastic_closure {r : ℝ} (h13 : 1 + r = r ^ 3) :
    ∀ n : ℕ, ∃ m, m ≥ n + 2 ∧ r ^ m = r ^ n + r ^ (n + 1) := by
  intro n
  refine ⟨n + 3, by omega, ?_⟩
  rw [pow_add, ← h13]
  ring

/-- **The plastic ladder fails full generation at rung 2.** No pair of
smaller rungs sums to `r²`: `2 ≠ r²` (else `r = 1`), `1 + r ≠ r²` (else
`r = 1`), and `2r ≠ r²` (else `r = 2`, contradicting `r³ = r + 1`). This is
why the witness is not a `BankedLadder`: the banked package's generation
field is exactly what excludes it. -/
theorem plastic_fails_generation_at_two {r : ℝ} (hr1 : 1 < r)
    (h13 : 1 + r = r ^ 3) :
    ∀ a b : ℕ, a ≤ b → b < 2 → r ^ 2 ≠ r ^ a + r ^ b := by
  intro a b hab hb2 hEq
  have hr0 : 0 < r := by linarith
  interval_cases b <;> interval_cases a <;> simp at hEq
  · -- r^2 = 2: then r^3 = 2r = r + 1, so r = 1
    have h2 : r ^ 2 = 2 := by linarith [hEq]
    have h3 : r ^ 3 = 2 * r := by
      calc r ^ 3 = r ^ 2 * r := by ring
        _ = 2 * r := by rw [h2]
    rw [← h13] at h3
    linarith
  · -- r^2 = 1 + r = r^3: then r^2 * (r - 1) = 0, but both factors positive
    have h2 : r ^ 2 = 1 + r := by linarith [hEq]
    rw [h13] at h2
    have hpos : 0 < r ^ 2 * (r - 1) := mul_pos (by nlinarith) (by linarith)
    have hexp : r ^ 2 * (r - 1) = r ^ 3 - r ^ 2 := by ring
    rw [hexp] at hpos
    have hz : r ^ 3 - r ^ 2 = 0 := by linarith [h2]
    linarith [hpos, hz]
  · -- r^2 = 2r: then r = 2, but 2^3 ≠ 2 + 1
    have h2 : r ^ 2 = 2 * r := by linarith [hEq]
    have hne : r ≠ 0 := hr0.ne'
    have h0' : r * (r - 2) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h hne
    · have hr2 : r = 2 := by linarith
      rw [hr2] at h13
      norm_num at h13

/-- **Headline: a positive mass gap does not force the recurrence.** There
exists a ladder with a positive spectral gap, adjacent closure, the tick, and
a ratio floor, which violates the adjacent recurrence and admits no ratio
floor above the plastic constant. Mass-spectrum stability reduced to its
φ-free content (a positive gap) is therefore insufficient to supply the
what-causes-time floor; the required input is the gap being *above*
`J(ρ_plastic)`, which no banked stability physics derives. -/
theorem mass_gap_insufficient_for_recurrence :
    ∃ (s : ℕ → ℝ) (ρ c : ℝ),
      (∀ n, 0 < s n) ∧ 1 < ρ ∧ ρ ^ 3 = ρ + 1 ∧
      (∀ n, ρ * s n ≤ s (n + 1)) ∧
      (∀ n, ∃ m, m ≥ n + 2 ∧ s m = s n + s (n + 1)) ∧
      (∃ d : ℝ, 0 < d ∧ ∀ n, d ≤ s (n + 1) - s n) ∧
      StepCostGap s c ∧
      (∀ ρ' : ℝ, 1 < ρ' → (∀ n, ρ' * s n ≤ s (n + 1)) → ρ' ^ 3 ≤ ρ' + 1) ∧
      ¬ (∀ n, s (n + 2) = s (n + 1) + s n) := by
  obtain ⟨r, hr1', h13'⟩ := PhiClosureSelection.plastic_ladder_exists
  have hr0' : 0 < r := by linarith
  refine ⟨fun n => r ^ n, r, Cost.Jcost r, (fun n => pow_pos hr0' n), hr1',
    by linarith [h13'], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    show r * r ^ n ≤ r ^ (n + 1)
    exact le_of_eq (pow_succ' r n).symm
  · intro n
    obtain ⟨m, hm, he⟩ := plastic_closure h13' n
    exact ⟨m, hm, he⟩
  · exact ⟨r - 1, by linarith, plastic_tick hr1'⟩
  · exact plastic_step_cost_gap hr1'
  · intro ρ' hρ' hfloor
    exact plastic_admits_no_floor_above_plastic hr1' h13' ρ' hρ'
      (fun n => by simpa using hfloor n)
  · intro h
    exact plastic_recurrence_violated hr1' h13' (fun n => by simpa using h n)

/-- **Uniform ladders need no floor: closure plus generation suffice.** If a
ladder has a uniform ratio `r > 1`, adjacent closure (even just at rung 0),
and full generation of rung 2, then `r = φ`. The generation pairing for rung
2 is one of `r² = 2`, `r² = 1 + r`, `r² = 2r`; the first and third contradict
closure (`r^m = 1 + r` with `m ≥ 2`), leaving `r² = 1 + r`, whose only root
above 1 is φ.

Read against the bridge theorem: on uniform ladders the growth floor is free,
so the floor premise of the what-causes-time chain is exactly the price of
dropping uniformity. -/
theorem uniform_closure_generation_forces_phi
    (s : ℕ → ℝ) (r : ℝ) (hr : 1 < r) (h0 : 0 < s 0)
    (hunif : ∀ n, s (n + 1) = r * s n)
    (hcl0 : ∃ m : ℕ, 2 ≤ m ∧ s m = s 0 + s 1)
    (hgen2 : ∃ a b : ℕ, a ≤ b ∧ b < 2 ∧ s 2 = s a + s b) :
    r = phi := by
  have hsn : ∀ n : ℕ, s n = r ^ n * s 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [hunif k, ih, pow_succ']; ring
  have hs0 : s 0 ≠ 0 := h0.ne'
  obtain ⟨m, hm2, hm⟩ := hcl0
  have hrm : r ^ m = 1 + r := by
    rw [hsn m, hsn 1, pow_one] at hm
    have e2 : s 0 + r * s 0 = (1 + r) * s 0 := by ring
    rw [e2] at hm
    exact mul_right_cancel₀ hs0 hm
  obtain ⟨a, b, hab, hb2, hgen⟩ := hgen2
  have hgen' : r ^ 2 = r ^ a + r ^ b := by
    rw [hsn 2, hsn a, hsn b] at hgen
    have e2 : r ^ a * s 0 + r ^ b * s 0 = (r ^ a + r ^ b) * s 0 := by ring
    rw [e2] at hgen
    exact mul_right_cancel₀ hs0 hgen
  interval_cases b <;> interval_cases a <;> simp at hgen'
  · -- r^2 = 2: closure gives r^m = 1 + r, m ≥ 2
    rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | hm3
    · rw [hrm] at hgen'
      linarith
    · have hle : r ^ 3 ≤ r ^ m := pow_le_pow_right₀ (by linarith : 1 ≤ r) hm3
      rw [hrm] at hle
      have hr3 : r ^ 3 = 2 * r := by rw [pow_succ, hgen']; ring
      linarith
  · -- r^2 = 1 + r: the golden equation; the only root above 1 is φ
    have hp : phi ^ 2 = phi + 1 := Constants.phi_sq_eq
    have hfact : (r - phi) * (r + phi - 1) = 0 := by
      have he : (r - phi) * (r + phi - 1) = (r ^ 2 - r) - (phi ^ 2 - phi) := by ring
      rw [he, hgen', hp]
      ring
    rcases mul_eq_zero.mp hfact with hrl | hrr
    · linarith
    · linarith [Constants.one_lt_phi]
  · -- r^2 = 2r: then r = 2, and 2^m = 3 is impossible for m ≥ 2
    have hne : r ≠ 0 := by linarith
    have h0' : r * (r - 2) = 0 := by
      have he : r * (r - 2) = r ^ 2 - 2 * r := by ring
      rw [he, hgen']; ring
    rcases mul_eq_zero.mp h0' with h | h
    · exact absurd h hne
    · have hr2 : r = 2 := by linarith
      rw [hr2] at hrm
      have hle : (4:ℝ) ≤ (2:ℝ) ^ m := by
        calc (4:ℝ) = (2:ℝ) ^ 2 := by norm_num
          _ ≤ (2:ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hm2
      linarith

#print axioms plastic_step_cost_gap
#print axioms plastic_admits_no_floor_above_plastic
#print axioms plastic_recurrence_violated
#print axioms plastic_tick
#print axioms plastic_closure
#print axioms plastic_fails_generation_at_two
#print axioms mass_gap_insufficient_for_recurrence
#print axioms uniform_closure_generation_forces_phi

end GrowthFloorPhysicsBoundary
end Foundation
end IndisputableMonolith
end
