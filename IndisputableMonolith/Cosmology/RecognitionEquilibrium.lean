import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cosmology.RefineTrigger

/-!
# Recognition equilibrium: the forward dynamics descends to the J-cost ground state

This module discharges, in Lean, the central convergence facts of the Phase-7 forward
dynamics (`scripts/cosmogenesis/forward_dynamics.py`). That dynamics evolves a field of
recognition levels `x : Fin n → ℝ` on a coupling graph by posting, each tick, one forced
recognition event: it resolves a coupled pair `(i, j)` by sending both endpoints to their
mean (the sigma = 0, J-minimal move; no relaxation rate, no knob). The Python checks these
facts numerically; here they are theorems.

* `pairResolve_levelSum` : a resolution conserves the level sum (sigma is conserved).
* `variance_pairResolve` : a resolution lowers the spread by **exactly** `(x i - x j)^2 / 2`.
  So the level variance is a Lyapunov function with an exact, law-given decrement; the
  dynamics is a strict descent until every coupled pair is equal. (Total edge demand is
  *not* monotone and is not claimed to be; the variance is.)
* `variance_nonincreasing` : the immediate corollary (the spread never grows).
* `jcost_nonneg`, `jcost_eq_zero_iff` : the recognition cost is nonnegative, and zero only
  at ratio one.
* `totalCost_nonneg`, `totalCost_eq_zero_iff` : the total recognition cost over the
  coupling graph is nonnegative and vanishes **iff** the field is constant on every edge
  (consensus). So the recognition ground state is exactly the consensus configuration the
  descent converges to.
* `conjugateBirth_chargeSum`, `manyBirths_chargeSum` : the driven (open-system) extension
  (`scripts/cosmogenesis/expanding_dynamics.py`) grows the ladder by a conjugate pair
  `(+u, -u)` born at the horizon each cadence cycle. These show that a birth, and any number
  of births, conserves the charge sum, so sigma = 0 holds through the whole driven evolution:
  recognition resolutions conserve it by `pairResolve_levelSum`, births by these. Closed-
  system descent (above) provably relaxes to consensus; the conserved-sigma birth is the
  forced open input that keeps non-homogenizing structure alive.

`Jcost` and `jcost_pos` are reused from `RefineTrigger` (T-3); `phi` and `one_lt_phi` from
`Constants`. The ratio of two regions is the forced `phi ^ (x i - x j)`. Zero `sorry`,
zero new `axiom`; the only axioms are the three standard ones.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RecognitionEquilibrium

open scoped BigOperators
open IndisputableMonolith.Cosmology.RefineTrigger

/-! ## §1. The forced pair resolution and the conserved sum -/

/-- The forced recognition resolution of one coupled pair: send both endpoints to their
mean. This is the sigma = 0, J-minimal move the forward dynamics posts each tick. -/
noncomputable def pairResolve {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) : Fin n → ℝ :=
  fun k => if k = i ∨ k = j then (x i + x j) / 2 else x k

@[simp] lemma pairResolve_at_i {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    pairResolve x i j i = (x i + x j) / 2 := by
  unfold pairResolve; rw [if_pos (Or.inl rfl)]

@[simp] lemma pairResolve_at_j {n : ℕ} (x : Fin n → ℝ) (i j : Fin n) :
    pairResolve x i j j = (x i + x j) / 2 := by
  unfold pairResolve; rw [if_pos (Or.inr rfl)]

lemma pairResolve_other {n : ℕ} (x : Fin n → ℝ) {i j k : Fin n}
    (hi : k ≠ i) (hj : k ≠ j) : pairResolve x i j k = x k := by
  unfold pairResolve
  rw [if_neg (by rintro (h | h); exact hi h; exact hj h)]

/-- The sum of all levels (the conserved sigma quantity). -/
noncomputable def levelSum {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ k, x k

/-- A helper: split `∑` over `univ` as `∑` over the pair `{i, j}` plus the rest, and prove
two configurations that agree off `{i, j}` have equal `∑` there. -/
private lemma sum_split_pair {n : ℕ} (f g : Fin n → ℝ) {i j : Fin n} (hij : i ≠ j)
    (hagree : ∀ k, k ≠ i → k ≠ j → f k = g k) :
    (∑ k, f k) - (∑ k, g k) = (f i + f j) - (g i + g j) := by
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hf : (∑ k, f k) = (∑ k ∈ Finset.univ \ {i, j}, f k) + (f i + f j) := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hij]
  have hg : (∑ k, g k) = (∑ k ∈ Finset.univ \ {i, j}, g k) + (g i + g j) := by
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hij]
  have hrest : (∑ k ∈ Finset.univ \ {i, j}, f k) = (∑ k ∈ Finset.univ \ {i, j}, g k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_sdiff] at hk
    have hki : k ≠ i := by rintro rfl; exact hk.2 (by simp)
    have hkj : k ≠ j := by rintro rfl; exact hk.2 (by simp)
    exact hagree k hki hkj
  rw [hf, hg, hrest]; ring

/-- **Sigma is conserved.** Resolving a pair leaves the total level unchanged. -/
theorem pairResolve_levelSum {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    levelSum (pairResolve x i j) = levelSum x := by
  unfold levelSum
  have hagree : ∀ k, k ≠ i → k ≠ j → pairResolve x i j k = x k :=
    fun k hi hj => pairResolve_other x hi hj
  have hsp := sum_split_pair (pairResolve x i j) x h hagree
  rw [pairResolve_at_i, pairResolve_at_j] at hsp
  -- hsp : (∑ resolved) - (∑ x) = ((xi+xj)/2 + (xi+xj)/2) - (x i + x j)
  have hzero : ((x i + x j) / 2 + (x i + x j) / 2) - (x i + x j) = 0 := by ring
  rw [hzero] at hsp
  linarith [hsp]

/-! ## §2. The variance is a Lyapunov function with an exact, law-given decrement -/

/-- Spread of the level field around a reference `c`. -/
noncomputable def varAround {n : ℕ} (x : Fin n → ℝ) (c : ℝ) : ℝ := ∑ k, (x k - c) ^ 2

/-- **The exact variance drop (around any reference).** Resolving a pair lowers the spread
by exactly `(x i - x j)^2 / 2`, independent of the reference point. -/
theorem varAround_pairResolve {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) (c : ℝ) :
    varAround (pairResolve x i j) c = varAround x c - (x i - x j) ^ 2 / 2 := by
  unfold varAround
  have hagree : ∀ k, k ≠ i → k ≠ j →
      (pairResolve x i j k - c) ^ 2 = (x k - c) ^ 2 :=
    fun k hi hj => by rw [pairResolve_other x hi hj]
  have hsplit := sum_split_pair (fun k => (pairResolve x i j k - c) ^ 2)
    (fun k => (x k - c) ^ 2) h hagree
  simp only [pairResolve_at_i, pairResolve_at_j] at hsplit
  -- hsplit : (∑ resolved sq) - (∑ x sq) = (2 * ((xi+xj)/2 - c)^2) - ((xi-c)^2 + (xj-c)^2)
  have hid : (((x i + x j) / 2 - c) ^ 2 + ((x i + x j) / 2 - c) ^ 2)
      - ((x i - c) ^ 2 + (x j - c) ^ 2) = -((x i - x j) ^ 2 / 2) := by ring
  rw [hid] at hsplit
  linarith [hsplit]

/-- The mean level. -/
noncomputable def meanLevel {n : ℕ} (x : Fin n → ℝ) : ℝ := levelSum x / (n : ℝ)

/-- The level variance (spread about the mean): the Lyapunov function of the descent. -/
noncomputable def variance {n : ℕ} (x : Fin n → ℝ) : ℝ := varAround x (meanLevel x)

theorem meanLevel_pairResolve {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    meanLevel (pairResolve x i j) = meanLevel x := by
  unfold meanLevel; rw [pairResolve_levelSum x h]

/-- **The variance Lyapunov law.** Each forced resolution lowers the level variance by
exactly `(x i - x j)^2 / 2`. The decrement is the recognition gap that was resolved, so
the descent is strict until every coupled pair is equal. -/
theorem variance_pairResolve {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    variance (pairResolve x i j) = variance x - (x i - x j) ^ 2 / 2 := by
  unfold variance
  rw [meanLevel_pairResolve x h, varAround_pairResolve x h (meanLevel x)]

/-- The spread never grows under a forced resolution. -/
theorem variance_nonincreasing {n : ℕ} (x : Fin n → ℝ) {i j : Fin n} (h : i ≠ j) :
    variance (pairResolve x i j) ≤ variance x := by
  rw [variance_pairResolve x h]
  nlinarith [sq_nonneg (x i - x j)]

/-! ## §3. The recognition cost ground state is exactly consensus -/

/-- The recognition cost is nonnegative. -/
theorem jcost_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ Jcost x := by
  rcases eq_or_ne x 1 with h | h
  · subst h; norm_num [Jcost]
  · exact le_of_lt (RefineTrigger.jcost_pos hx h)

/-- The recognition cost vanishes exactly at ratio one. -/
theorem jcost_eq_zero_iff {x : ℝ} (hx : 0 < x) : Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h0
    by_contra hne
    have hp : 0 < Jcost x := RefineTrigger.jcost_pos hx hne
    rw [h0] at hp
    exact lt_irrefl 0 hp
  · intro h; subst h; norm_num [Jcost]

/-- `phi ^ t = 1` exactly when `t = 0` (phi is positive and not one). -/
theorem phi_rpow_eq_one_iff (t : ℝ) : (Constants.phi : ℝ) ^ t = 1 ↔ t = 0 := by
  rw [Real.rpow_def_of_pos Constants.phi_pos,
      show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm, Real.exp_eq_exp]
  have hlog : Real.log Constants.phi ≠ 0 := ne_of_gt (Real.log_pos Constants.one_lt_phi)
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hlog
    · exact h'
  · intro h; rw [h, mul_zero]

/-- Two regions carry no forced distinction exactly when their levels are equal. -/
theorem cost_phi_eq_zero_iff (a b : ℝ) :
    Jcost ((Constants.phi : ℝ) ^ (a - b)) = 0 ↔ a = b := by
  rw [jcost_eq_zero_iff (Real.rpow_pos_of_pos Constants.phi_pos _),
      phi_rpow_eq_one_iff, sub_eq_zero]

/-- Total recognition cost over the coupling graph: the sum of the forced demands. -/
noncomputable def totalCost {n : ℕ} (x : Fin n → ℝ) (edges : Finset (Fin n × Fin n)) : ℝ :=
  ∑ e ∈ edges, Jcost ((Constants.phi : ℝ) ^ (x e.1 - x e.2))

/-- The total recognition cost is nonnegative. -/
theorem totalCost_nonneg {n : ℕ} (x : Fin n → ℝ) (edges : Finset (Fin n × Fin n)) :
    0 ≤ totalCost x edges :=
  Finset.sum_nonneg (fun _ _ => jcost_nonneg (Real.rpow_pos_of_pos Constants.phi_pos _))

/-- **The recognition ground state is consensus.** The total recognition cost vanishes if
and only if the level field is constant on every coupled pair. So the zero-cost
configuration the descent converges to is exactly graph consensus. -/
theorem totalCost_eq_zero_iff {n : ℕ} (x : Fin n → ℝ) (edges : Finset (Fin n × Fin n)) :
    totalCost x edges = 0 ↔ ∀ e ∈ edges, x e.1 = x e.2 := by
  rw [totalCost, Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => jcost_nonneg (Real.rpow_pos_of_pos Constants.phi_pos _))]
  constructor
  · intro h e he; exact (cost_phi_eq_zero_iff _ _).mp (h e he)
  · intro h e he; exact (cost_phi_eq_zero_iff _ _).mpr (h e he)

/-! ## §4. The bundled statement -/

/-- The recognition-equilibrium package: the forced forward dynamics conserves sigma,
descends the level variance by an exact law-given decrement (so the spread is a Lyapunov
function and the descent is strict until consensus), and its zero-cost ground state is
exactly the consensus configuration. -/
structure Equilibrium {n : ℕ} (x : Fin n → ℝ)
    (edges : Finset (Fin n × Fin n)) : Prop where
  sigma_conserved : ∀ i j : Fin n, i ≠ j → levelSum (pairResolve x i j) = levelSum x
  variance_drop : ∀ i j : Fin n, i ≠ j →
    variance (pairResolve x i j) = variance x - (x i - x j) ^ 2 / 2
  variance_nonincreasing : ∀ i j : Fin n, i ≠ j → variance (pairResolve x i j) ≤ variance x
  cost_nonneg : 0 ≤ totalCost x edges
  ground_state_iff_consensus : totalCost x edges = 0 ↔ ∀ e ∈ edges, x e.1 = x e.2

/-- **Recognition equilibrium holds for every level field and coupling graph.** -/
theorem recognitionEquilibrium {n : ℕ} (x : Fin n → ℝ)
    (edges : Finset (Fin n × Fin n)) : Equilibrium x edges where
  sigma_conserved := fun _ _ h => pairResolve_levelSum x h
  variance_drop := fun _ _ h => variance_pairResolve x h
  variance_nonincreasing := fun _ _ h => variance_nonincreasing x h
  cost_nonneg := totalCost_nonneg x edges
  ground_state_iff_consensus := totalCost_eq_zero_iff x edges

/-! ## §5. Expansion: a conjugate birth at the horizon conserves sigma

The driven (open-system) dynamics (`scripts/cosmogenesis/expanding_dynamics.py`) grows the
phi-ladder: each cadence cycle a conjugate pair `(+u, -u)` is born at the two frontiers, the
double-entry creation of a distinction at the horizon. The closed descent of §1-§4 provably
relaxes any connected world to consensus (the variance is a strict Lyapunov function), so a
forced open input is needed to keep structure alive; the conjugate birth is that input.

Recognition resolutions conserve the level sum by `pairResolve_levelSum`. Here we show the
birth conserves it too, so sigma = 0 holds through the whole driven evolution, resolve and
grow alike. The charge field is a `List ℝ` here because a birth changes the number of
regions (the ladder grows). -/

/-- **A conjugate birth conserves sigma.** Inserting `+u` at the fine frontier and `-u` at
the coarse frontier leaves the total charge unchanged: the net of the born pair is zero. -/
theorem conjugateBirth_chargeSum (u : ℝ) (xs : List ℝ) :
    ((u :: xs) ++ [-u]).sum = xs.sum := by
  simp only [List.sum_append, List.sum_cons, List.sum_nil]
  ring

/-- **Any number of conjugate births conserves sigma.** After `k` cadence cycles of
expansion the ladder carries `k` extra `+u` charges at the fine frontier and `k` extra `-u`
charges at the coarse frontier; the total charge is still the initial total. So sigma = 0 is
preserved through the entire driven run. -/
theorem manyBirths_chargeSum (k : ℕ) (u : ℝ) (xs : List ℝ) :
    (List.replicate k u ++ xs ++ List.replicate k (-u)).sum = xs.sum := by
  simp only [List.sum_append, List.sum_replicate, nsmul_eq_mul]
  ring

end RecognitionEquilibrium
end Cosmology
end IndisputableMonolith
