import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Masses.GoldenFoldForcing
import IndisputableMonolith.Masses.GoldenMonodromyReturn

/-!
# J-cost selection of the golden linking number (sourcing Live Bet 1)

`Masses/GoldenMonodromyReturn.lean` banked the algebraic heart of the monodromy front-end: the
`exchange ∘ transport(k)` return map has `trace = k` (the linking number), `det = −1` (the
structural swap), satisfies the `k`-metallic relation `F² = kF + I`, and is golden **iff** `k = 1`.
It left **one** named OPEN residual (Live Bet 1): *which* kernel principle forces the linking number
`k` of the two forced 8-tick cycles to be `1` rather than any other integer.

This module discharges that residual **to a J-cost minimization**, i.e. to the kernel principle
(recognition cost is the unique reciprocal cost `J`, and physics minimizes it). It does **not** stop
at "assume `k = 1`". It proves, for the *free* integer `k`:

1. **The eigenvalue is the metallic mean.** `metallicMean k = (k + √(k²+4))/2` is the positive real
   root of the return map's characteristic polynomial `X² − kX − 1`
   (`metallicMean_is_returnMap_eigenvalue`), so it is the genuine dominant eigenvalue, not an
   unrelated number.
2. **The exact recognition cost.** `foldCost k := J(metallicMean k) = √(k²+4)/2 − 1`
   (`foldCost_eq`). At `k = 1` this is `J(φ) = φ − 3/2` (consistent with
   `Constants.Jcost_phi_val`); at `k = 0` it is `0`.
3. **Positive-growth characterization.** `1 < metallicMean k ↔ 1 ≤ k` over ℤ
   (`metallicMean_growth_iff`). `metallicMean k` is the *positive* eigenvalue, i.e. the mass-ladder
   ratio (masses are positive). Requiring it to exceed `1` (an expanding tower) forces `k ≥ 1`. The
   unlinked `k = 0` case is the pure exchange **involution** (eigenvalues `±1`, `m = 1`, no tower).
   The `k ≤ −1` case is the sharp point (see the honest status): the map still **expands** (spectral
   radius `= metallicMean|k| > 1`, e.g. `φ` at `k = −1`), but its *dominant* eigenvalue is
   **negative** (`dominant_eigenvalue_negative_of_le_neg_one`), so its tower ratio alternates sign
   and is excluded by **mass positivity**, not by any failure to expand.
4. **The selection.** Among growth folds, `foldCost` is strictly increasing in `k`
   (`foldCost_strictMono`), so `k = 1` is the **unique minimal-recognition-cost growth fold**
   (`generation_fold_selects_golden`, `foldCost_strict_above_one`). Its eigenvalue is `φ` and its
   return map is the banked `goldenMulZ`.

## Honest status

- Every declaration is THEOREM-grade (no `sorry`; `#print axioms` = Mathlib base only).
- What is now **proved**: *among positive-growth folds (positive eigenvalue `m > 1`, so `k ≥ 1`) of
  the banked `exchange ∘ transport(k)` family, the one of least recognition cost `J` is exactly
  `k = 1` (golden, eigenvalue φ)* (`generation_fold_selects_golden`, `foldCost_strict_above_one`).
- **The `J`-cost is even in `k`** (`foldCost_even`: it depends only on `k²`), so
  `foldCost(−1) = foldCost(1)` (`foldCost_neg_one_eq_one`). **`J`-minimization alone does NOT break
  the `k = ±1` degeneracy.** This is stated, not hidden. The split into two named forcing inputs is
  therefore honest:
    1. **`J`-minimization** selects `|k| = 1` as the unique cheapest growth linking magnitude
       (proved: `foldCost_strict_above_one`).
    2. **A positive, unbounded mass ladder** selects `k ≥ 1`, hence the `+1` branch. This is genuine
       physical content, proved *at the level of the actual ladder*, not merely at mode-sign level.
       `mass_ladder_forces_ge_one`: if `m : ℕ → ℝ` obeys the return-map recurrence
       `m(n+2) = k·m(n+1) + m n`, has `m n > 0` for all `n`, and is unbounded, then `k ≥ 1`.
- **The mode-sign argument's pinhole is closed.** A prior version leaned on
  `dominant_eigenvalue_negative_of_le_neg_one` (at `k = −1` the dominant eigenvalue is `−φ`). That is
  corroborating but not airtight: the sequence `m n = (1/φ)ⁿ` is *positive* and solves the `k = −1`
  recurrence, yet it **decays** (bounded), so mode-sign alone leaves it. `mass_ladder_forces_ge_one`
  closes the pinhole by proving every positive `k ≤ 0` ladder is **bounded** (both interleaved
  subsequences are non-increasing, `mass_ladder_bounded_of_nonpos`), so it can never be the required
  unbounded generation tower. The `(1/φ)ⁿ` witness is exactly such a bounded ladder.
- The discreteness `k : ℤ` is load-bearing: for a real `0 < k < 1` the positive eigenvalue already
  exceeds `1` and a positive unbounded ladder exists. The linking number being an integer (an
  `H₁ ≅ ℤ` winding) is what makes `k = 0` the only sub-unit option and forces the jump to `k = 1`.
- What remains a named physical residual: *the generation fold is a positive, unbounded mass ladder*
  (`hpos` + `hub` in `mass_ladder_forces_ge_one`). This is not faked as a theorem — it is the honest
  physical input (masses are positive; there is a real infinite generation tower). Given it, `k = 1`
  is forced with no residual `k = 1` assumption: `golden_unique_min_cost_ladder` proves every
  `k ≠ 1` positive-unbounded ladder has strictly greater recognition cost. Without growth, `J` is
  minimized by the trivial `k = 0` involution (`foldCost_zero = 0`); that is the only escape, and it
  is not a tower.
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenFoldCostSelection

open Constants
open Polynomial
open IndisputableMonolith.Masses.GoldenFoldForcing
open IndisputableMonolith.Masses.GoldenMonodromyReturn

/-! ## The metallic mean: the dominant eigenvalue of the return map -/

/-- **Metallic mean at linking number `k`.** `m(k) = (k + √(k²+4))/2`, the positive real root of the
return map's characteristic polynomial `X² − kX − 1`. `m(1) = φ`, `m(0) = 1`, `m(2) = 1 + √2`
(silver). -/
noncomputable def metallicMean (k : ℝ) : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2

/-- `√(k²+4) > k`: the discriminant root dominates the trace (for any real `k`, since `k²+4 > k²`
whenever `k ≥ 0`, and `√(k²+4) ≥ 0 > k` when `k < 0`). -/
theorem sqrt_disc_gt (k : ℝ) : k < Real.sqrt (k ^ 2 + 4) := by
  rcases le_or_gt 0 k with hk | hk
  · have h1 : Real.sqrt (k ^ 2) < Real.sqrt (k ^ 2 + 4) :=
      Real.sqrt_lt_sqrt (by positivity) (by linarith)
    rwa [Real.sqrt_sq hk] at h1
  · exact lt_of_lt_of_le hk (Real.sqrt_nonneg _)

/-- `|k| < √(k²+4)`: the discriminant root dominates the trace in magnitude. -/
theorem abs_lt_sqrt_disc (k : ℝ) : |k| < Real.sqrt (k ^ 2 + 4) := by
  rw [show |k| = Real.sqrt (k ^ 2) from (Real.sqrt_sq_eq_abs k).symm]
  exact Real.sqrt_lt_sqrt (by positivity) (by linarith)

/-- **The metallic mean is positive** for every linking number. -/
theorem metallicMean_pos (k : ℝ) : 0 < metallicMean k := by
  unfold metallicMean
  have h := abs_lt_sqrt_disc k
  have h2 : -k ≤ |k| := neg_le_abs k
  linarith

theorem metallicMean_ne_zero (k : ℝ) : metallicMean k ≠ 0 := ne_of_gt (metallicMean_pos k)

/-- **The metallic mean satisfies its mode equation** `m² = k·m + 1` (it is a root of
`X² − kX − 1`). This is the scalar shadow of the return map's `k`-metallic relation. -/
theorem metallicMean_root (k : ℝ) : (metallicMean k) ^ 2 = k * metallicMean k + 1 := by
  have hnn : (0 : ℝ) ≤ k ^ 2 + 4 := by positivity
  have hs : Real.sqrt (k ^ 2 + 4) ^ 2 = k ^ 2 + 4 := Real.sq_sqrt hnn
  unfold metallicMean
  linear_combination (1 / 4 : ℝ) * hs

/-- `m(1) = φ`, the golden ratio. -/
theorem metallicMean_one : metallicMean 1 = phi := by
  unfold metallicMean Constants.phi
  norm_num

/-- `m(0) = 1`: the unlinked case is the neutral (order-2 involution) eigenvalue. -/
theorem metallicMean_zero : metallicMean 0 = 1 := by
  unfold metallicMean
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [h4]

/-! ## The other (negative) root: the branch mass-positivity excludes

The characteristic polynomial `X² − kX − 1` has two real roots: the positive `metallicMean k` and
the negative `otherRoot k`. Their product is the determinant `−1`. This is the object that makes the
`k = ±1` degeneracy honest: at `k = −1` the map still expands (spectral radius `φ`), but its
larger-magnitude (*dominant*) eigenvalue is the **negative** `otherRoot (−1) = −φ`, so a mass ladder
built from it would alternate sign. Mass positivity excludes it. -/

/-- **The other root** of the characteristic polynomial `X² − kX − 1`: `o(k) = (k − √(k²+4))/2`. It
is the second eigenvalue of the return map, always **negative**, with `m·o = −1`. -/
noncomputable def otherRoot (k : ℝ) : ℝ := (k - Real.sqrt (k ^ 2 + 4)) / 2

/-- **The other root is negative** for every linking number: `√(k²+4) > k`. -/
theorem otherRoot_neg (k : ℝ) : otherRoot k < 0 := by
  unfold otherRoot
  have := sqrt_disc_gt k
  linarith

/-- **The other root satisfies the same mode equation** `o² = k·o + 1` (it is the second root of
`X² − kX − 1`). -/
theorem otherRoot_root (k : ℝ) : (otherRoot k) ^ 2 = k * otherRoot k + 1 := by
  have hnn : (0 : ℝ) ≤ k ^ 2 + 4 := by positivity
  have hs : Real.sqrt (k ^ 2 + 4) ^ 2 = k ^ 2 + 4 := Real.sq_sqrt hnn
  unfold otherRoot
  linear_combination (1 / 4 : ℝ) * hs

/-- **The two roots multiply to `−1`** (the determinant of the return map). -/
theorem metallicMean_mul_otherRoot (k : ℝ) : metallicMean k * otherRoot k = -1 := by
  have hnn : (0 : ℝ) ≤ k ^ 2 + 4 := by positivity
  have hs : Real.sqrt (k ^ 2 + 4) ^ 2 = k ^ 2 + 4 := Real.sq_sqrt hnn
  unfold metallicMean otherRoot
  linear_combination (-(1 : ℝ) / 4) * hs

/-- `o(−1) = −φ`: at `k = −1` the dominant (larger-magnitude) eigenvalue is `−φ`, negative. This is
the concrete witness that `k = −1` expands but with the wrong sign. -/
theorem otherRoot_neg_one : otherRoot (-1) = -phi := by
  have h5 : ((-1 : ℝ)) ^ 2 + 4 = 5 := by norm_num
  unfold otherRoot Constants.phi
  rw [h5]; ring

/-! ## The bridge: the metallic mean is the return map's eigenvalue -/

/-- **Non-circularity bridge.** `metallicMean k` is a real root of the return map's characteristic
polynomial (mapped to ℝ). So the recognition cost below is the cost of the *genuine dominant
eigenvalue* of the banked geometric object, not a number chosen to make the answer come out. -/
theorem metallicMean_is_returnMap_eigenvalue (k : ℤ) :
    ((GoldenMonodromyReturn.returnMap k).charpoly.map (Int.castRingHom ℝ)).eval
      (metallicMean (k : ℝ)) = 0 := by
  rw [GoldenMonodromyReturn.returnMap_charpoly]
  have hroot := metallicMean_root (k : ℝ)
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_mul,
    Polynomial.map_one, Polynomial.map_intCast, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_intCast, eq_intCast]
  linear_combination hroot

/-! ## The exact recognition cost of the fold -/

/-- **The recognition cost of the fold at linking number `k`**: the J-cost of its dominant
eigenvalue. -/
noncomputable def foldCost (k : ℝ) : ℝ := Cost.Jcost (metallicMean k)

/-- `m⁻¹ = m − k` (from the mode equation `m² = km+1`, so `m·(m−k) = 1`). -/
theorem metallicMean_inv (k : ℝ) : (metallicMean k)⁻¹ = metallicMean k - k := by
  have hroot := metallicMean_root k
  have hne := metallicMean_ne_zero k
  have key : metallicMean k * (metallicMean k - k) = 1 := by linear_combination hroot
  have hmi : metallicMean k * (metallicMean k)⁻¹ = 1 := mul_inv_cancel₀ hne
  exact mul_left_cancel₀ hne (hmi.trans key.symm)

/-- `m + m⁻¹ = √(k²+4)`: the sum of the two reciprocal eigenvalues is the discriminant root. -/
theorem metallicMean_add_inv (k : ℝ) :
    metallicMean k + (metallicMean k)⁻¹ = Real.sqrt (k ^ 2 + 4) := by
  rw [metallicMean_inv]
  unfold metallicMean
  ring

/-- **The exact cost formula.** `foldCost k = √(k²+4)/2 − 1`. Everything downstream (the values, the
monotonicity, the selection of `k = 1`) reads off this closed form. -/
theorem foldCost_eq (k : ℝ) : foldCost k = Real.sqrt (k ^ 2 + 4) / 2 - 1 := by
  unfold foldCost Cost.Jcost
  rw [metallicMean_add_inv]

/-- `foldCost 1 = J(φ) = φ − 3/2` (consistent with `Constants.Jcost_phi_val`). -/
theorem foldCost_one : foldCost 1 = phi - 3 / 2 := by
  unfold foldCost
  rw [metallicMean_one]
  exact Constants.Jcost_phi_val

/-- `foldCost 0 = 0`: the unlinked involution has zero recognition cost — the global minimum over
*all* `k`, which is exactly why the growth requirement (below) is needed to select `k = 1`. -/
theorem foldCost_zero : foldCost 0 = 0 := by
  unfold foldCost
  rw [metallicMean_zero, Cost.Jcost]
  norm_num

/-- **The J-cost is even in `k`**: `foldCost k = foldCost (−k)`. It depends only on `k²` (via the
discriminant `√(k²+4)`). This is *why* J-minimization alone cannot break the `k = ±1` degeneracy —
the tie is broken by mass positivity, not by cost. Stated honestly, not hidden. -/
theorem foldCost_even (k : ℝ) : foldCost (-k) = foldCost k := by
  rw [foldCost_eq, foldCost_eq]
  ring_nf

/-- `foldCost (−1) = foldCost 1 = φ − 3/2`: the two unit linking numbers have **identical**
recognition cost. J-minimization is degenerate here; mass positivity is what selects `+1`. -/
theorem foldCost_neg_one_eq_one : foldCost (-1) = phi - 3 / 2 := by
  rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, foldCost_even, foldCost_one]

/-! ## Growth characterization: which folds build the tower -/

/-- For `k ≥ 1` the fold **expands** (`m > 1`), so it can build the φ-ladder tower. -/
theorem metallicMean_gt_one_of_ge_one (k : ℝ) (hk : 1 ≤ k) : 1 < metallicMean k := by
  unfold metallicMean
  have := sqrt_disc_gt k
  linarith

/-- For `k ≤ 0` the **positive** eigenvalue does not exceed `1` (`m ≤ 1`): `k = 0` is the neutral
involution (`m = 1`), and for `k < 0` the positive root `m < 1`. (The *map* need not contract for
`k ≤ −1` — its negative root then dominates with magnitude `> 1`; see
`dominant_eigenvalue_negative_of_le_neg_one`. This lemma is only about the positive branch, which is
the physical mass-ladder ratio.) -/
theorem metallicMean_le_one_of_le_zero (k : ℝ) (hk : k ≤ 0) : metallicMean k ≤ 1 := by
  unfold metallicMean
  have h2k : (0 : ℝ) ≤ 2 - k := by linarith
  have hsq : Real.sqrt (k ^ 2 + 4) ≤ 2 - k := by
    rw [show (2 - k) = Real.sqrt ((2 - k) ^ 2) from (Real.sqrt_sq h2k).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [hk]
  linarith

/-- **Positive-growth ⟺ unit-or-greater linking (over ℤ).** `1 < metallicMean k ↔ 1 ≤ k`, where
`metallicMean k` is the *positive* eigenvalue (the mass-ladder ratio). Requiring a positive expanding
tower forces `k ≥ 1`: the unlinked `k = 0` involution has `m = 1` (no tower), and for `k ≤ −1` the
positive root has `m < 1` while the dominant root is negative
(`dominant_eigenvalue_negative_of_le_neg_one`), so no positive tower exists. -/
theorem metallicMean_growth_iff (k : ℤ) : 1 < metallicMean (k : ℝ) ↔ 1 ≤ k := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
    exact absurd h (not_lt.mpr (metallicMean_le_one_of_le_zero _ hk0))
  · intro h
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    exact metallicMean_gt_one_of_ge_one _ this

/-! ## Eigenvalue dominance: the sign of the growth mode

The two eigenvalues are `metallicMean k > 0` and `otherRoot k < 0`. Their magnitudes differ by
`|otherRoot k| − |metallicMean k| = −k`. So for `k ≥ 1` the **positive** root dominates (a positive
mass ladder), and for `k ≤ −1` the **negative** root dominates (an alternating-sign ladder, excluded
by mass positivity). This is the precise mechanism that breaks the `J`-cost `k = ±1` tie. -/

/-- **For `k ≤ −1` the dominant eigenvalue is the negative one.** Concretely
`metallicMean k < |otherRoot k| = −otherRoot k`: the negative root has strictly larger magnitude, so
the growth mode alternates sign. A ladder of positive masses cannot be built from it — mass
positivity excludes every `k ≤ −1`, leaving `J`-minimization to pick `k = 1` among the `k ≥ 1`
branch. -/
theorem dominant_eigenvalue_negative_of_le_neg_one (k : ℝ) (hk : k ≤ -1) :
    metallicMean k < -otherRoot k := by
  unfold metallicMean otherRoot
  linarith

/-- **For `k ≥ 1` the dominant eigenvalue is the positive one** (`metallicMean k > |otherRoot k|`):
the growth mode is the positive metallic mean, giving a positive mass ladder. -/
theorem dominant_eigenvalue_positive_of_ge_one (k : ℝ) (hk : 1 ≤ k) :
    -otherRoot k < metallicMean k := by
  unfold metallicMean otherRoot
  linarith

/-! ## The J-cost selection of `k = 1` -/

/-- **Monotonicity of the cost.** For `0 ≤ a ≤ b`, `foldCost a ≤ foldCost b`. -/
theorem foldCost_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : foldCost a ≤ foldCost b := by
  rw [foldCost_eq, foldCost_eq]
  have : Real.sqrt (a ^ 2 + 4) ≤ Real.sqrt (b ^ 2 + 4) := by
    apply Real.sqrt_le_sqrt
    nlinarith [ha, hab]
  linarith

/-- **Strict monotonicity of the cost.** For `0 ≤ a < b`, `foldCost a < foldCost b`. -/
theorem foldCost_strictMono {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : foldCost a < foldCost b := by
  rw [foldCost_eq, foldCost_eq]
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have : Real.sqrt (a ^ 2 + 4) < Real.sqrt (b ^ 2 + 4) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [ha, hab, mul_pos (sub_pos.mpr hab) (by linarith : (0:ℝ) < b + a)]
  linarith

/-- **The selection theorem.** Among growth-producing folds (`1 < metallicMean k`, i.e. `k ≥ 1`),
`k = 1` (golden) has the least recognition cost `J`. This is the J-minimization that sources Live
Bet 1: the kernel selects the golden linking number because it is the cheapest expanding fold. -/
theorem generation_fold_selects_golden (k : ℤ) (hgrow : 1 < metallicMean (k : ℝ)) :
    foldCost 1 ≤ foldCost (k : ℝ) := by
  have hk1 : 1 ≤ k := (metallicMean_growth_iff k).mp hgrow
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  simpa using foldCost_mono (by norm_num : (0:ℝ) ≤ 1) h1

/-- **Strict selection above `k = 1`.** For every non-golden growth fold `k ≥ 2`, the cost is
strictly larger than the golden cost, so `k = 1` is the **unique** minimizer among growth folds. -/
theorem foldCost_strict_above_one (k : ℤ) (hk : 2 ≤ k) : foldCost 1 < foldCost (k : ℝ) := by
  have h1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : (1:ℤ) < k)
  exact foldCost_strictMono (by norm_num : (0:ℝ) ≤ 1) h1

/-! ## The sequence-level selection: a positive, unbounded mass ladder forces `k ≥ 1`

The mode-sign argument above (`dominant_eigenvalue_negative_of_le_neg_one`) is corroborating but
not by itself airtight: a *positive* sequence can satisfy the `k ≤ 0` recurrence without the
positive eigenvalue dominating. The sharp witness is `m n = (1/φ)ⁿ`, which is positive and solves
the `k = −1` recurrence `m(n+2) = −m(n+1) + m(n)` (since `1/φ² + 1/φ = 1`), yet **decays** — it is
bounded. So mode-sign alone leaves that pinhole.

The airtight statement is at the level of the actual mass ladder. The return map acting on the
state `(m(n), m(n−1))` produces `(m(n+1), m(n))` with `m(n+1) = k·m(n) + m(n−1)`, so iterating the
banked geometric object on the ladder IS the recurrence below. We prove: **any positive sequence
obeying that recurrence with `k ≤ 0` is bounded**, hence a positive *unbounded* mass tower forces
`k ≥ 1`. This closes the `(1/φ)ⁿ` pinhole: that sequence is positive but bounded, so it never
satisfies the unboundedness hypothesis, and no positive unbounded `k ≤ 0` ladder exists. -/

/-- **Two-step non-increase for `k ≤ 0`.** If a positive sequence obeys the return-map recurrence
`m(n+2) = kr·m(n+1) + m n` with `kr ≤ 0`, then `m(n+2) ≤ m n`: the linking term `kr·m(n+1)` is
non-positive (negative linking against a positive mass), so the ladder cannot climb across two
steps. -/
theorem mass_ladder_two_step_le (kr : ℝ) (m : ℕ → ℝ)
    (hrec : ∀ n, m (n + 2) = kr * m (n + 1) + m n)
    (hpos : ∀ n, 0 < m n) (hk : kr ≤ 0) (n : ℕ) : m (n + 2) ≤ m n := by
  have hp : (0 : ℝ) ≤ m (n + 1) := (hpos (n + 1)).le
  have hkn : kr * m (n + 1) ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨hk, hp⟩)
  have hr := hrec n
  linarith

/-- **A positive `k ≤ 0` mass ladder is bounded** by `max (m 0) (m 1)`. The two interleaved
subsequences (even and odd index) are each non-increasing by `mass_ladder_two_step_le`, so neither
can exceed its seed. This is the core fact that kills every non-positive linking number. -/
theorem mass_ladder_bounded_of_nonpos (kr : ℝ) (m : ℕ → ℝ)
    (hrec : ∀ n, m (n + 2) = kr * m (n + 1) + m n)
    (hpos : ∀ n, 0 < m n) (hk : kr ≤ 0) :
    ∀ n, m n ≤ max (m 0) (m 1) := by
  have step := mass_ladder_two_step_le kr m hrec hpos hk
  have pair : ∀ n, m n ≤ max (m 0) (m 1) ∧ m (n + 1) ≤ max (m 0) (m 1) := by
    intro n
    induction n with
    | zero => exact ⟨le_max_left _ _, le_max_right _ _⟩
    | succ i ih =>
        refine ⟨ih.2, ?_⟩
        calc m (i + 2) ≤ m i := step i
          _ ≤ max (m 0) (m 1) := ih.1
  intro n
  exact (pair n).1

/-- **The sequence-level selection theorem (closes Live Bet 1 mass-positivity).** If the mass ladder
`m : ℕ → ℝ` is generated by the banked return map (recurrence `m(n+2) = k·m(n+1) + m n`), has
**strictly positive** masses, and is **unbounded** (a genuine infinite generation tower), then the
integer linking number satisfies `k ≥ 1`.

This is the airtight replacement for the mode-sign heuristic. Its two physical hypotheses are
exactly the honest inputs named in the module docstring: mass positivity (`hpos`) and an actual
growth tower (`hub`). Crucially it needs `k : ℤ` — for a *real* `0 < k < 1` the positive eigenvalue
already exceeds `1` and a positive unbounded ladder exists, so the discreteness of the linking
number is load-bearing, not decorative. -/
theorem mass_ladder_forces_ge_one (k : ℤ) (m : ℕ → ℝ)
    (hrec : ∀ n, m (n + 2) = (k : ℝ) * m (n + 1) + m n)
    (hpos : ∀ n, 0 < m n)
    (hub : ∀ B : ℝ, ∃ n, B < m n) : 1 ≤ k := by
  by_contra hc
  push_neg at hc
  have hk0 : (k : ℝ) ≤ 0 := by exact_mod_cast (by omega : k ≤ 0)
  obtain ⟨n, hn⟩ := hub (max (m 0) (m 1))
  exact absurd hn (not_lt.mpr (mass_ladder_bounded_of_nonpos (k : ℝ) m hrec hpos hk0 n))

/-- **Non-vacuity witness: the golden ladder `φⁿ` is a genuine positive, unbounded `k = 1` ladder.**
The powers of the golden metallic mean solve the `k = 1` recurrence (because `φ² = φ + 1`), are
strictly positive, and are unbounded (`φ > 1`). So the hypotheses of `mass_ladder_forces_ge_one`
are satisfiable and the `k = 1` branch is realized — the selection theorem is not vacuous, and the
Fibonacci/golden generation tower is an explicit instance of it. -/
theorem golden_ladder_witness :
    (∀ n, (metallicMean 1) ^ (n + 2)
        = (1 : ℝ) * (metallicMean 1) ^ (n + 1) + (metallicMean 1) ^ n)
    ∧ (∀ n, 0 < (metallicMean 1) ^ n)
    ∧ (∀ B : ℝ, ∃ n, B < (metallicMean 1) ^ n) := by
  have hpos : 0 < metallicMean 1 := metallicMean_pos 1
  have hsq : (metallicMean 1) ^ 2 = 1 * metallicMean 1 + 1 := metallicMean_root 1
  have h1lt : (1 : ℝ) < metallicMean 1 := metallicMean_gt_one_of_ge_one 1 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · intro n
    have : (metallicMean 1) ^ (n + 2) = (metallicMean 1) ^ n * (metallicMean 1) ^ 2 := by
      ring
    rw [this, hsq]; ring
  · intro n; exact pow_pos hpos n
  · intro B
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h1lt
    exact ⟨n, hn⟩

/-- **The capstone: `k = 1` is the unique least-cost positive unbounded mass ladder.** Combining the
sequence-level selection (`mass_ladder_forces_ge_one`, forcing `k ≥ 1` from mass positivity and
genuine growth) with the J-cost strict monotonicity (`foldCost_strict_above_one`, forcing `k = 1`
among `k ≥ 1`): for a positive, unbounded mass ladder generated by the return map, **every** linking
number `k ≠ 1` carries strictly greater recognition cost. So the golden linking number `k = 1` is
the unique minimizer. This is the full discharge of Live Bet 1 through the two named forcing inputs,
with no residual `k = 1` assumption. -/
theorem golden_unique_min_cost_ladder (k : ℤ) (m : ℕ → ℝ)
    (hrec : ∀ n, m (n + 2) = (k : ℝ) * m (n + 1) + m n)
    (hpos : ∀ n, 0 < m n)
    (hub : ∀ B : ℝ, ∃ n, B < m n)
    (hne : k ≠ 1) : foldCost 1 < foldCost (k : ℝ) := by
  have hk1 : 1 ≤ k := mass_ladder_forces_ge_one k m hrec hpos hub
  exact foldCost_strict_above_one k (by omega)

/-! ## Certificate -/

/-- THEOREM-grade certificate: the golden linking number `k = 1` is the **unique least-recognition-
cost growth-producing** member of the banked `exchange ∘ transport(k)` monodromy family; its
eigenvalue is `φ` and its return map is the banked `goldenMulZ`. This routes the Live-Bet-1 residual
of `GoldenMonodromyReturn` through J-minimization (the kernel principle), leaving only the physical
requirement that the generation fold be growth-producing (`m > 1`) as a named, corroborated
residual. -/
structure GoldenFoldCostCert where
  eigen_is_root : ∀ k : ℤ,
    ((GoldenMonodromyReturn.returnMap k).charpoly.map (Int.castRingHom ℝ)).eval
      (metallicMean (k : ℝ)) = 0
  cost_formula : ∀ k : ℝ, foldCost k = Real.sqrt (k ^ 2 + 4) / 2 - 1
  golden_cost : foldCost 1 = phi - 3 / 2
  unlinked_cost_zero : foldCost 0 = 0
  golden_eigenvalue_is_phi : metallicMean 1 = phi
  growth_iff_linking : ∀ k : ℤ, 1 < metallicMean (k : ℝ) ↔ 1 ≤ k
  golden_minimizes_growth : ∀ k : ℤ, 1 < metallicMean (k : ℝ) → foldCost 1 ≤ foldCost (k : ℝ)
  strict_above_golden : ∀ k : ℤ, 2 ≤ k → foldCost 1 < foldCost (k : ℝ)
  selected_return_map : GoldenMonodromyReturn.returnMap 1 = goldenMulZ
  -- The honest two-input structure: J-cost is even (ties k = ±1), and mass positivity
  -- (dominant eigenvalue sign) breaks the tie in favour of k = +1.
  cost_even : ∀ k : ℝ, foldCost (-k) = foldCost k
  neg_one_ties_one : foldCost (-1) = foldCost 1
  other_root_negative : ∀ k : ℝ, otherRoot k < 0
  roots_mult_det : ∀ k : ℝ, metallicMean k * otherRoot k = -1
  dominant_negative_below : ∀ k : ℝ, k ≤ -1 → metallicMean k < -otherRoot k
  dominant_positive_above : ∀ k : ℝ, 1 ≤ k → -otherRoot k < metallicMean k
  -- The airtight sequence-level selection: a positive, unbounded mass ladder generated by the
  -- return map forces k ≥ 1 (closing the m n = (1/φ)ⁿ pinhole in the mode-sign argument), and
  -- combined with strict cost monotonicity, k = 1 is the unique least-cost such ladder.
  positive_unbounded_ladder_forces_ge_one : ∀ (k : ℤ) (m : ℕ → ℝ),
    (∀ n, m (n + 2) = (k : ℝ) * m (n + 1) + m n) → (∀ n, 0 < m n) →
    (∀ B : ℝ, ∃ n, B < m n) → 1 ≤ k
  golden_unique_min_cost : ∀ (k : ℤ) (m : ℕ → ℝ),
    (∀ n, m (n + 2) = (k : ℝ) * m (n + 1) + m n) → (∀ n, 0 < m n) →
    (∀ B : ℝ, ∃ n, B < m n) → k ≠ 1 → foldCost 1 < foldCost (k : ℝ)
  -- Non-vacuity: the golden ladder φⁿ is a genuine positive, unbounded k = 1 ladder, so the
  -- selection hypotheses are satisfiable and the k = 1 branch is realized (differential test).
  golden_ladder_realized :
    (∀ n, (metallicMean 1) ^ (n + 2)
        = (1 : ℝ) * (metallicMean 1) ^ (n + 1) + (metallicMean 1) ^ n)
    ∧ (∀ n, 0 < (metallicMean 1) ^ n)
    ∧ (∀ B : ℝ, ∃ n, B < (metallicMean 1) ^ n)

theorem goldenFoldCostCert_holds : Nonempty GoldenFoldCostCert :=
  ⟨{ eigen_is_root := metallicMean_is_returnMap_eigenvalue
     cost_formula := foldCost_eq
     golden_cost := foldCost_one
     unlinked_cost_zero := foldCost_zero
     golden_eigenvalue_is_phi := metallicMean_one
     growth_iff_linking := metallicMean_growth_iff
     golden_minimizes_growth := generation_fold_selects_golden
     strict_above_golden := foldCost_strict_above_one
     selected_return_map := GoldenMonodromyReturn.returnMap_one_eq_goldenMulZ
     cost_even := foldCost_even
     neg_one_ties_one := by rw [foldCost_neg_one_eq_one, foldCost_one]
     other_root_negative := otherRoot_neg
     roots_mult_det := metallicMean_mul_otherRoot
     dominant_negative_below := dominant_eigenvalue_negative_of_le_neg_one
     dominant_positive_above := dominant_eigenvalue_positive_of_ge_one
     positive_unbounded_ladder_forces_ge_one := mass_ladder_forces_ge_one
     golden_unique_min_cost := golden_unique_min_cost_ladder
     golden_ladder_realized := golden_ladder_witness }⟩

end GoldenFoldCostSelection
end Masses
end IndisputableMonolith
