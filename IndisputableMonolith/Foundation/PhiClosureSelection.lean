import Mathlib
import IndisputableMonolith.Cost.GeometricRoot
import IndisputableMonolith.Foundation.PhiForcingDerived

/-!
# φ-Closure Selection: why the ledger closes at level 2

Origin: the geometric-root live bet's leg 4 (plan:
`plans/Geometric_Root_Proof_Plan_20260730.html`, attack prompt:
`plans/Geometric_Root_Leg4_Session_Prompt_20260730.txt`). The bet: the
golden ratio should fall out of structure, not out of a minimality posture.
The library's existing derivations take closure as a hypothesis:
`PhiForcingDerived` assumes `1 + r = r²`, and `HierarchyMinimality` packages
closure at the first nontrivial index as the `minimalClosure` field.

## What is proved here (THEOREM, kernel-checked, axioms printed below)

1. **Uniform scaling + adjacent composition forces φ directly**
   (`ratio_eq_phi_of_uniform_adjacent_composition`): a positive scale
   sequence with a constant inter-level ratio `r > 1` whose levels satisfy
   the adjacent additive recurrence `s_{n+2} = s_{n+1} + s_n` has `r = φ`.
   No closure hypothesis: the recurrence and the uniform ratio force the
   golden equation algebraically.
2. **Higher closures leave orphan rungs** (`high_closure_orphan`): if
   `1 + r = r^k` with `k ≥ 3`, then no pair of rungs composes to `r²`:
   the rung `r²` is a scale that no composition of ledger events produces.
3. **The φ ladder is fully generated** (`phi_rung_composed`): if
   `1 + r = r²`, every rung `m ≥ 2` is the adjacent composition of the two
   preceding rungs.
4. **Composability of the second rung selects k = 2**
   (`closure_level_two_of_rung_two_composed`): among all adjacent-closed
   ladders (`1 + r = r^k`, `k ≥ 2`), requiring `r²` to be a composition of
   two rungs forces `k = 2` and `r = φ`. The selecting premise is "every
   posted scale is earned by composition" (no orphan postings), a structural
   completeness condition, not a minimality posture.
5. **The excess-minimization route is dead, by measurement**
   (`closure_cost_strictly_decreasing`, `plastic_cheaper_than_phi`): the
   per-closure cost `J(1 + r_k)` is strictly decreasing in the closure level
   `k` — the `k = 3` ladder (plastic constant) exists and is strictly
   cheaper than the `k = 2` ladder. Cost-minimization over closure levels
   selects nothing finite (the infimum `J(2) = 1/4` is approached as
   `k → ∞`, the same trivialization phenomenon as the tick theorem). This
   kills the sub-route "the J-cost excess selects k = 2 by minimization"
   and is why the selection above is structural (generation), not variational.

## Honest status

The ladder form (a uniform inter-level ratio) remains a premise here, as it
is in every existing derivation in the library (it is the zero-free-parameter
scaling condition; its own discharge is a separate problem). What this module
removes is the *closure* assumption and the "minimal integer coefficients"
posture: closure is now a theorem from composition structure, and the
selection of level 2 is generation completeness, not minimality.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PhiClosureSelection

open Real Constants

/-! ## Arithmetic helpers (local, no name hunts) -/

theorem one_le_pow_of_one_le {r : ℝ} (hr : 1 ≤ r) (n : ℕ) : 1 ≤ r ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h : (1 : ℝ) * 1 ≤ r ^ k * r :=
      mul_le_mul ih hr (by norm_num) (pow_nonneg (by linarith) k)
    simpa using h

theorem pow_le_pow_of_le {r : ℝ} (hr : 1 ≤ r) {m n : ℕ} (h : m ≤ n) :
    r ^ m ≤ r ^ n := by
  have e : r ^ n = r ^ m * r ^ (n - m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e]
  have h1 : 1 ≤ r ^ (n - m) := one_le_pow_of_one_le hr _
  calc r ^ m = r ^ m * 1 := by ring
    _ ≤ r ^ m * r ^ (n - m) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg (by linarith) m)

/-- Injectivity of `n ↦ r^n` for `r > 1`, via `log`. -/
theorem pow_inj_right {r : ℝ} (hr : 1 < r) {a b : ℕ} (h : r ^ a = r ^ b) :
    a = b := by
  have hl : Real.log r ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have h2 : (a : ℝ) * Real.log r = (b : ℝ) * Real.log r := by
    have h3 := congrArg Real.log h
    simpa [Real.log_pow] using h3
  have h4 : (a : ℝ) = (b : ℝ) := mul_right_cancel₀ hl h2
  exact_mod_cast h4

/-! ## The four-way case analysis for a composed second rung -/

/-- If `r^a + r^b = r²` with `r > 1`, the pair `(a, b)` is one of `(0,0)`,
`(0,1)`, `(1,0)`, `(1,1)`, with the corresponding consequence for `r`. -/
theorem rung_two_sum_cases {r : ℝ} (hr : 1 < r) {a b : ℕ}
    (hab : r ^ a + r ^ b = r ^ 2) :
    (a = 0 ∧ b = 0 ∧ r ^ 2 = 2) ∨ (a = 0 ∧ b = 1 ∧ 1 + r = r ^ 2) ∨
      (a = 1 ∧ b = 0 ∧ 1 + r = r ^ 2) ∨ (a = 1 ∧ b = 1 ∧ r = 2) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have ha : a ≤ 1 := by
    by_contra h
    push_neg at h
    have hb2 : r ^ 2 ≤ r ^ a := pow_le_pow_of_le (le_of_lt hr) h
    have hpos : 0 < r ^ b := pow_pos hr0 b
    linarith [hb2, hpos, hab]
  have hb : b ≤ 1 := by
    by_contra h
    push_neg at h
    have hb2 : r ^ 2 ≤ r ^ b := pow_le_pow_of_le (le_of_lt hr) h
    have hpos : 0 < r ^ a := pow_pos hr0 a
    linarith [hb2, hpos, hab]
  interval_cases a <;> interval_cases b
  · -- (0,0): 1 + 1 = r²
    simp at hab
    exact Or.inl ⟨rfl, rfl, by linarith [hab]⟩
  · -- (0,1): 1 + r = r²
    simp at hab
    exact Or.inr (Or.inl ⟨rfl, rfl, by linarith [hab]⟩)
  · -- (1,0): r + 1 = r²
    simp at hab
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by linarith [hab]⟩))
  · -- (1,1): r + r = r² → r = 2
    simp at hab
    right
    right
    right
    refine ⟨rfl, rfl, ?_⟩
    have h2r : r * (r - 2) = 0 := by nlinarith [hab]
    rcases mul_eq_zero.mp h2r with h | h
    · linarith [hr, h]
    · linarith [h]

/-! ## Higher closures leave orphan rungs -/

/-- **Orphan theorem.** If the ladder closes at level `k ≥ 3` (`1 + r = r^k`),
then `r²` is not the composition of any two rungs: it is an orphan scale,
postable but never produced by composing ledger events. -/
theorem high_closure_orphan {r : ℝ} {k : ℕ} (hr : 1 < r) (hk : 3 ≤ k)
    (hclose : 1 + r = r ^ k) (a b : ℕ) :
    r ^ a + r ^ b ≠ r ^ 2 := by
  intro hab
  rcases rung_two_sum_cases hr hab with ⟨_, _, h2⟩ | ⟨_, _, h12⟩ | ⟨_, _, h12⟩ | ⟨_, _, hr2⟩
  · -- r² = 2, so r³ = 2r ≤ r^k, giving 1 + r ≥ 2r, i.e. 1 ≥ r.
    have hk3 : r ^ 3 ≤ r ^ k := pow_le_pow_of_le (le_of_lt hr) hk
    have hr3 : r ^ 3 = 2 * r := by
      calc r ^ 3 = r * r ^ 2 := by ring
        _ = r * 2 := by rw [h2]
        _ = 2 * r := by ring
    linarith [hk3, hr3, hclose, hr]
  · -- 1 + r = r² and 1 + r = r^k force k = 2.
    have hkk : r ^ k = r ^ 2 := by rw [← h12, hclose]
    have := pow_inj_right hr hkk
    omega
  · have hkk : r ^ k = r ^ 2 := by rw [← h12, hclose]
    have := pow_inj_right hr hkk
    omega
  · -- r = 2: closure gives 3 = 2^k ≥ 8.
    have hk3 : r ^ 3 ≤ r ^ k := pow_le_pow_of_le (le_of_lt hr) hk
    rw [hr2] at hk3 hclose
    norm_num at hk3 hclose
    linarith [hk3, hclose]

/-! ## The φ ladder is fully generated -/

/-- **Generation theorem.** On a ladder closed at level 2 (`1 + r = r²`),
every rung beyond the first two is the adjacent composition of the two
preceding rungs. No orphans: every posted scale is earned. -/
theorem phi_rung_composed {r : ℝ} (h : 1 + r = r ^ 2) (m : ℕ) (hm : 2 ≤ m) :
    r ^ m = r ^ (m - 1) + r ^ (m - 2) := by
  have e : r ^ m = r ^ (m - 2) * r ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have e3 : r ^ (m - 2) * r = r ^ (m - 1) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e, ← h, mul_add, mul_one, e3]
  ring

/-! ## Composability of the second rung selects level 2 -/

/-- **Selection theorem.** Among adjacent-closed ladders (`1 + r = r^k`,
`k ≥ 2`), the ones in which the second rung is a composition of two rungs
are exactly the `k = 2` ladders, and then `r = φ`. The selecting premise is
generation completeness (no orphan scales), not minimality. -/
theorem closure_level_two_of_rung_two_composed {r : ℝ} {k : ℕ}
    (hr : 1 < r) (hk : 2 ≤ k) (hclose : 1 + r = r ^ k)
    (a b : ℕ) (hab : r ^ a + r ^ b = r ^ 2) :
    k = 2 ∧ r = phi := by
  rcases rung_two_sum_cases hr hab with ⟨_, _, h2⟩ | ⟨_, _, h12⟩ | ⟨_, _, h12⟩ | ⟨_, _, hr2⟩
  · -- r² = 2: exclude both k = 2 and k ≥ 3.
    rcases (le_iff_eq_or_lt.mp hk) with hkk | hkk
    · -- k = 2: closure gives 1 + r = 2, i.e. r = 1.
      subst hkk
      exfalso
      linarith [hclose, h2, hr]
    · -- k ≥ 3: r³ = 2r ≤ r^k gives 1 ≥ r.
      have hk3 : r ^ 3 ≤ r ^ k := pow_le_pow_of_le (le_of_lt hr) hkk
      have hr3 : r ^ 3 = 2 * r := by
        calc r ^ 3 = r * r ^ 2 := by ring
          _ = r * 2 := by rw [h2]
          _ = 2 * r := by ring
      exfalso
      linarith [hk3, hr3, hclose, hr]
  · -- 1 + r = r²: closure gives r^k = r², so k = 2; then r = φ.
    have hkk : r ^ k = r ^ 2 := by rw [← h12, hclose]
    have hk2 := pow_inj_right hr hkk
    exact ⟨hk2, PhiForcingDerived.phi_forcing_complete r (by linarith) (by linarith) h12⟩
  · have hkk : r ^ k = r ^ 2 := by rw [← h12, hclose]
    have hk2 := pow_inj_right hr hkk
    exact ⟨hk2, PhiForcingDerived.phi_forcing_complete r (by linarith) (by linarith) h12⟩
  · -- r = 2: exclude both k = 2 and k ≥ 3.
    rcases (le_iff_eq_or_lt.mp hk) with hkk | hkk
    · subst hkk
      rw [hr2] at hclose
      norm_num at hclose
    · have hk3 : r ^ 3 ≤ r ^ k := pow_le_pow_of_le (le_of_lt hr) hkk
      rw [hr2] at hk3 hclose
      norm_num at hk3 hclose
      linarith [hk3, hclose]

/-! ## Uniform scaling + adjacent composition forces φ (no closure assumed) -/

/-- **Direct forcing.** A positive scale sequence with a constant inter-level
ratio `r > 1` (uniform scaling: one ratio, no free parameters) satisfying the
adjacent additive recurrence (each level composes its two neighbours: binary
posting) has ratio `φ`. Closure is not assumed; the golden equation falls
out of the two premises algebraically. -/
theorem ratio_eq_phi_of_uniform_adjacent_composition {s : ℕ → ℝ} {r : ℝ}
    (h0 : 0 < s 0) (hr : 1 < r)
    (hunif : ∀ n, s (n + 1) = r * s n)
    (hadj : ∀ n, s (n + 2) = s (n + 1) + s n) :
    r = phi := by
  have h1 : s 1 = r * s 0 := hunif 0
  have h2u : s 2 = r * s 1 := hunif 1
  have h2a : s 2 = s 1 + s 0 := hadj 0
  rw [h1] at h2a h2u
  -- r * (r * s 0) = r * s 0 + s 0
  have hs0 : s 0 ≠ 0 := ne_of_gt h0
  have hfact : s 0 * (r ^ 2 - r - 1) = 0 := by nlinarith [h2u, h2a]
  rcases mul_eq_zero.mp hfact with h | h
  · exact absurd h hs0
  · have hsq : 1 + r = r ^ 2 := by nlinarith [h]
    exact PhiForcingDerived.phi_forcing_complete r (by linarith) (by linarith) hsq

/-! ## The excess-minimization route is dead, by measurement -/

/-- The telescoping factor bound: for `1 ≤ x < y` and `n ≥ 2`,
`y^n - x^n ≥ 2(y - x)`. -/
theorem geom_sum_factor_bound {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) {n : ℕ}
    (hn : 2 ≤ n) :
    (y - x) * 2 ≤ y ^ n - x ^ n := by
  have hfact0 := geom_sum₂_mul x y n
  have hfact : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (y - x)
      = y ^ n - x ^ n := by
    have e1 : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (y - x)
        = - ((∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y)) := by ring
    rw [e1, hfact0]
    ring
  have hy1 : 1 ≤ y := le_trans hx (le_of_lt hxy)
  have hsum : (n : ℝ) ≤ ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) := by
    calc (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : 1 ≤ x ^ i := one_le_pow_of_one_le hx i
          have h2 : 1 ≤ y ^ (n - 1 - i) := one_le_pow_of_one_le hy1 _
          have h3 : (1 : ℝ) * 1 ≤ x ^ i * y ^ (n - 1 - i) :=
            mul_le_mul h1 h2 (by norm_num) (by linarith)
          simpa using h3
  have hyx : (0 : ℝ) < y - x := by linarith
  calc (y - x) * 2 ≤ (y - x) * n := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hyx)
        exact_mod_cast hn
    _ = (n : ℝ) * (y - x) := by ring
    _ ≤ (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (y - x) :=
        mul_le_mul_of_nonneg_right hsum (le_of_lt hyx)
    _ = y ^ n - x ^ n := hfact

/-- The closure polynomial `x^n - x - 1` is strictly increasing on `[1, ∞)`
for `n ≥ 2`. -/
theorem closurePoly_strictMono {x y : ℝ} (hx : 1 ≤ x) (hxy : x < y) {n : ℕ}
    (hn : 2 ≤ n) :
    x ^ n - x - 1 < y ^ n - y - 1 := by
  have h := geom_sum_factor_bound hx hxy hn
  linarith

/-- `cosh` is strictly monotone on `[0, ∞)`, from the difference identity
banked in `Cost.GeometricRoot`. -/
theorem cosh_strictMono_on_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    Real.cosh x < Real.cosh y := by
  have h := Cost.GeometricRoot.cosh_sub_cosh x y
  have hA : 0 < Real.sinh ((y + x) / 2) := Cost.GeometricRoot.sinh_pos_of_pos (by linarith)
  have hB : 0 < Real.sinh ((y - x) / 2) := Cost.GeometricRoot.sinh_pos_of_pos (by linarith)
  have hpos : 0 < 2 * Real.sinh ((y + x) / 2) * Real.sinh ((y - x) / 2) := by
    positivity
  linarith

/-- **Route-kill measurement.** The per-closure cost `J(1 + r)` is strictly
decreasing as the closure level rises: for any two closure ladders at
consecutive levels, the higher-level ladder has the cheaper closure.
Cost-minimization therefore does not select `k = 2`; it selects nothing
finite. This kills the sub-route "the J-cost excess selects the closure
level by minimization." -/
theorem closure_cost_strictly_decreasing {r s : ℝ} {k : ℕ}
    (hr : 1 < r) (hrc : 1 + r = r ^ (k + 2))
    (hs : 1 < s) (hsc : 1 + s = s ^ (k + 3)) :
    Cost.Jcost (1 + s) < Cost.Jcost (1 + r) := by
  have hsr : s < r := by
    by_contra h
    push_neg at h
    rcases lt_or_eq_of_le h with hlt | heq
    · -- r < s: strict monotonicity of the closure polynomial gives
      -- f_{k+3}(r) < f_{k+3}(s) = 0, but f_{k+3}(r) = r² - 1 > 0.
      have h1 : r ^ (k + 3) - r - 1 < s ^ (k + 3) - s - 1 :=
        closurePoly_strictMono (le_of_lt hr) hlt (by omega)
      have hfs : s ^ (k + 3) - s - 1 = 0 := by
        have e : s ^ (k + 3) = 1 + s := by rw [← hsc]
        linarith
      have hfr : r ^ (k + 3) - r - 1 = r ^ 2 - 1 := by
        have e0 : k + 3 = (k + 2) + 1 := by omega
        have e : r ^ (k + 3) = r * r ^ (k + 2) := by rw [e0, pow_succ']
        rw [e, ← hrc]
        ring
      nlinarith [h1, hfs, hfr, hr,
        mul_pos (sub_pos.mpr hr) (by linarith : (0 : ℝ) < r + 1)]
    · -- r = s: then r^{k+2} = r^{k+3}, impossible.
      rw [← heq] at hsc
      have e1 : r ^ (k + 2) = r ^ (k + 3) := by rw [← hrc, ← hsc]
      have := pow_inj_right hr e1
      omega
  have hlog : Real.log (1 + s) < Real.log (1 + r) :=
    Real.log_lt_log (by linarith) (by linarith)
  have hc : Real.cosh (Real.log (1 + s)) < Real.cosh (Real.log (1 + r)) :=
    cosh_strictMono_on_nonneg (Real.log_nonneg (by linarith)) hlog
  have e1 : Cost.Jcost (1 + s) = Real.cosh (Real.log (1 + s)) - 1 :=
    Cost.GeometricRoot.jcost_eq_cosh_log_sub_one (by linarith)
  have e2 : Cost.Jcost (1 + r) = Real.cosh (Real.log (1 + r)) - 1 :=
    Cost.GeometricRoot.jcost_eq_cosh_log_sub_one (by linarith)
  linarith [e1, e2, hc]

/-- The `k = 3` closure ladder exists: `1 + r = r³` has a root above 1
(the plastic constant), by the intermediate value theorem. -/
theorem plastic_ladder_exists : ∃ r : ℝ, 1 < r ∧ 1 + r = r ^ 3 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc (1 : ℝ) 2) :=
    ((continuous_pow 3).sub continuous_id |>.sub continuous_const).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo ((1 : ℝ) ^ 3 - 1 - 1) ((2 : ℝ) ^ 3 - 2 - 1) := by
    constructor <;> norm_num
  have hivt := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont hmem
  obtain ⟨r, hr, hfr⟩ := hivt
  refine ⟨r, hr.1, ?_⟩
  have h0 : r ^ 3 - r - 1 = 0 := hfr
  linarith

/-- The concrete witness for the route-kill: the plastic ladder exists and
its closure is strictly cheaper than the φ closure. -/
theorem plastic_cheaper_than_phi :
    ∃ r : ℝ, 1 < r ∧ 1 + r = r ^ 3 ∧
      Cost.Jcost (1 + r) < Cost.Jcost (1 + phi) := by
  obtain ⟨r, hr, hrc⟩ := plastic_ladder_exists
  refine ⟨r, hr, hrc, ?_⟩
  have hphi2 : 1 + phi = phi ^ 2 := by linarith [phi_sq_eq]
  have h := closure_cost_strictly_decreasing (k := 0) one_lt_phi
    (by simpa using hphi2) hr (by simpa using hrc)
  exact h

end PhiClosureSelection
end Foundation
end IndisputableMonolith

#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.high_closure_orphan
#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.phi_rung_composed
#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.closure_level_two_of_rung_two_composed
#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.ratio_eq_phi_of_uniform_adjacent_composition
#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.closure_cost_strictly_decreasing
#print axioms IndisputableMonolith.Foundation.PhiClosureSelection.plastic_cheaper_than_phi
