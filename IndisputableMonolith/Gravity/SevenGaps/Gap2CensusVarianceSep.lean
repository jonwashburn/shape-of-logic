import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusEnsembleLimit
import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusFirstMoments

/-!
# Gap 2 / C11 / A50: the residual variance separation (TARGET 2)

The A49 arc bounded the anomaly fraction by the raw second-moment ratio:
`q(c) ≤ ‖n_loop‖²/‖n_proper‖² = mechanismBound c`.  That bound wastes the
structure of the problem.  The loop count has conditional mean `k/n` on each
`(n, k)` cell, and the count span `{nV, nE, nT}` sees only `(n, k, t)` data,
so the centered loop count `n_loop − k/n` is *orthogonal to the whole count
span*.  The projection of `n_loop` onto the span therefore equals the
projection of the conditional-mean function `m(n,k) = k/n`, and Pythagoras
splits the residual exactly:

  `‖r(n_loop)‖² = ‖n_loop − m‖² + ‖r(m)‖²`
                = `E_μ[Var(n_loop ∣ n,k)] + ‖r(m)‖²`
                = `(nsum c − msqSum c)/m0sum c + ‖r(m)‖²`,

where `msqSum c = E_μ[(k/n)²]·m0sum c` is the census second moment of the
conditional mean.  The first summand is the *variance object* of A36
section 4: per cell it is `k(n−1)n^(2k−2)`, against `≈ c²·n^(2k)` for the
proper second moment at the saddle, which is where the factor
`(log c)/(2c²)` in the sharp rate comes from.  The second summand is the
residual of the mean function, nearly absorbed by the span.

## What is proved here (kernel strength, no new axioms, no sorry)

* `sum_centered_cell`: the centered first-moment identity,
  `Σ_j cellCount n k j·(j − k/n) = 0`, the cell-level content of
  "the count span cannot see the centered loop count".
* `inner_obsV_sub_obsM`, `inner_obsE_sub_obsM`, `inner_obsT_sub_obsM`: the
  three census orthogonality statements `⟪count, n_loop − m⟫ = 0`.
* `obsL_sub_obsM_mem_orthogonal`: `n_loop − m ∈ countSpanᗮ`.
* `msqSum`, `inner_obsL_obsM`, `norm_sq_obsM`: the second moment of the
  conditional mean, `⟪n_loop, m⟫ = ‖m‖² = msqSum c / m0sum c`.
* `starProjection_obsL_eq_coe`, `resid_obsL_eq`: the projections agree, so
  `r(n_loop) = (n_loop − m) + r(m)`.
* `norm_sq_resid_obsL`: **the variance separation** (TARGET 2),
  `‖r(n_loop)‖² = ‖n_loop − m‖² + ‖r(m)‖²`.
* `nvarSum`, `norm_sq_sub_obsM`: the variance piece is the evaluated sum
  `(nsum c − msqSum c)/m0sum c`.
* `qfrac_eq_resid_ratio`, `qfrac_eval`: **qfrac as an evaluated ratio**
  (TARGET 2), turning the A49 bound into an identity:
  `q(c) = (nvarSum c + ‖r(m)‖²·m0sum c) / dsum c`.
* `norm_sq_resid_le_of_mem_span`: the residual is minimal over the span,
  the workhorse for one-sided bounds on `‖r(m)‖²` with explicit test
  functions.

All results audit to the base triple `[propext, Classical.choice, Quot.sound]`
(`#print axioms` at the end of the file).
-/

namespace Gap2CensusVarianceSep

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
  Gap2CensusFirstMoments Gap2AnomalyAsymptotics Finset
open scoped Gap2CensusProductForm Nat RealInnerProductSpace

/-- The conditional-mean observable `m(n,k) = k/n` (the mean of the loop
count on its cell), as an element of `L²(μ_c)`.  At `n = 0` the real
division gives `k/0 = 0`, matching the conditional mean of the empty (and
the `k = 0`) cells, which carry no mass anyway. -/
noncomputable def obsM (c : ℕ) : L2fun c := fun x => (x.2.1.1 : ℝ) / (x.1.1 : ℝ)

/-!
## Section 1: the centered cell identity and census orthogonality
-/

/-- The first-moment identity, division-free: `loopMeanSum·n = k·n^(2k)`.
This is the form in which the cell identity enters the centered sum and the
mean-square computation. -/
theorem loopMeanSum_mul (n k : ℕ) : loopMeanSum n k * n = k * n ^ (2 * k) := by
  rw [loopMeanSum_eq]
  rcases k with _ | m
  · simp
  · conv_rhs => rw [show 2 * (m + 1) = (2 * (m + 1) - 1) + 1 from by omega, pow_succ]
    rw [mul_assoc]

/-- **The centered first-moment identity.**  On every cell, the loop count
centered at its conditional mean sums to zero against the cell weight:
`Σ_j cellCount n k j·(j − k/n) = 0`.  At `n ≥ 1` this is the first-moment
identity `Σ j·cellCount = k·n^(2k−1)` against the margin `Σ cellCount =
n^(2k)`; at `n = 0` the cell is empty (or `k = 0`, where the centered count
is `0 − 0/0 = 0`). -/
theorem sum_centered_cell (n k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * ((j : ℝ) - (k : ℝ) / n)) = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases k with _ | m
    · rw [Finset.sum_range_one]
      simp [cellCount]
    · exact Finset.sum_eq_zero fun j _ => by
        rw [cellCount_zero_left (by omega : 1 ≤ m + 1) j]
        simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hsplit : (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * ((j : ℝ) - (k : ℝ) / n))
        = (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * (j : ℝ))
          - (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * ((k : ℝ) / n)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hmean : (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * (j : ℝ))
        = (loopMeanSum n k : ℝ) := by
      have hcast : ∀ j : ℕ, (cellCount n k j : ℝ) * (j : ℝ)
          = ((j * cellCount n k j : ℕ) : ℝ) := fun j => by push_cast; ring
      rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Nat.cast_sum]
      simp only [loopMeanSum]
    have hmargin : (∑ j ∈ Finset.range (k + 1), (cellCount n k j : ℝ) * ((k : ℝ) / n))
        = (n : ℝ) ^ (2 * k) * ((k : ℝ) / n) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, margin_count, Nat.cast_pow]
    have hR : (loopMeanSum n k : ℝ) = (k : ℝ) * (n : ℝ) ^ (2 * k) / n :=
      (eq_div_iff_mul_eq hnR).2 (by exact_mod_cast loopMeanSum_mul n k)
    rw [hsplit, hmean, hmargin, hR]
    field_simp [hnR]
    ring

/-- The centered identity summed against the full product-form weight with an
arbitrary `t`-dependent factor: the `(j, t)`-slice of any
`⟪count, n_loop − m⟫` vanishes. -/
theorem sum_centered_weighted (c n k : ℕ) (w : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (w t * ((j : ℝ) - (k : ℝ) / n)))
    = 0 := by
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (∑ t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (w t * ((j : ℝ) - (k : ℝ) / n)))
      = (∑ t ∈ Finset.range (c + 1), w t) *
          ((cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * ((j : ℝ) - (k : ℝ) / n)) := by
    intro j _
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hjsum : (∑ j ∈ Finset.range (k + 1),
      (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * ((j : ℝ) - (k : ℝ) / n)) = 0 := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, sum_centered_cell]
    simp
  rw [hjsum, mul_zero]

/-- The vertex count is orthogonal to the centered loop count in `L²(μ_c)`. -/
theorem inner_obsV_sub_obsM (c : ℕ) : ⟪obsV c, obsL c - obsM c⟫ = 0 := by
  rw [inner_apply]
  refine (expect_eq_product_sum c (fun n k j _t =>
      (n : ℝ) * ((j : ℝ) - (k : ℝ) / n))).trans ?_
  have hnum : (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
      ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
          * ((n : ℝ) * ((j : ℝ) - (k : ℝ) / n))
      = 0) := by
    refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun k _ => ?_
    exact sum_centered_weighted c n k (fun _ => (n : ℝ))
  rw [hnum, zero_div]

/-- The edge count is orthogonal to the centered loop count in `L²(μ_c)`. -/
theorem inner_obsE_sub_obsM (c : ℕ) : ⟪obsE c, obsL c - obsM c⟫ = 0 := by
  rw [inner_apply]
  refine (expect_eq_product_sum c (fun n k j _t =>
      (k : ℝ) * ((j : ℝ) - (k : ℝ) / n))).trans ?_
  have hnum : (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
      ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
          * ((k : ℝ) * ((j : ℝ) - (k : ℝ) / n))
      = 0) := by
    refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun k _ => ?_
    exact sum_centered_weighted c n k (fun _ => (k : ℝ))
  rw [hnum, zero_div]

/-- The tet count is orthogonal to the centered loop count in `L²(μ_c)`. -/
theorem inner_obsT_sub_obsM (c : ℕ) : ⟪obsT c, obsL c - obsM c⟫ = 0 := by
  rw [inner_apply]
  refine (expect_eq_product_sum c (fun n k j t =>
      (t : ℝ) * ((j : ℝ) - (k : ℝ) / n))).trans ?_
  have hnum : (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
      ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ))
          * ((t : ℝ) * ((j : ℝ) - (k : ℝ) / n))
      = 0) := by
    refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun k _ => ?_
    exact sum_centered_weighted c n k (fun t => (t : ℝ))
  rw [hnum, zero_div]

/-- **The centered loop count is orthogonal to the whole count span.**
This is the structural heart of the variance separation: the count span sees
only `(n, k, t)` data, and `n_loop − k/n` has conditional mean zero on every
`(n, k)` cell. -/
theorem obsL_sub_obsM_mem_orthogonal (c : ℕ) :
    obsL c - obsM c ∈ (countSpan (obsV c) (obsE c) (obsT c))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  unfold countSpan at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact inner_obsV_sub_obsM c
    · exact inner_obsE_sub_obsM c
    · exact inner_obsT_sub_obsM c
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy =>
    rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx =>
    rw [inner_smul_left, hx, mul_zero]

/-!
## Section 2: the second moment of the conditional mean
-/

/-- The mean-square sum `MS(c) = Σ_{n,k} (k/n)²·n^(2k)/(n!·k!)`: the census
second moment of the conditional mean `m = k/n`, as a product-form sum.  The
real division by `n` makes the empty `n = 0` cells contribute `0`, matching
the weight they carry. -/
noncomputable def msqSum (c : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
    ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))

theorem msqSum_nonneg (c : ℕ) : 0 ≤ msqSum c :=
  Finset.sum_nonneg fun _n _ => Finset.sum_nonneg fun _k _ =>
    div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (ffact_nonneg _) (ffact_nonneg _))

/-- The cell-level second moment of the conditional mean, two ways:
`(k/n)·Σ_j j·cellCount = (k/n)²·Σ_j cellCount`, both sides being
`k²·n^(2k−2)` for `n ≥ 1` and `0` at `n = 0`. -/
theorem msq_cell_id (n k : ℕ) :
    (k : ℝ) / n * (loopMeanSum n k : ℝ) = ((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
    have hR : (loopMeanSum n k : ℝ) = (k : ℝ) * (n : ℝ) ^ (2 * k) / n :=
      (eq_div_iff_mul_eq hnR).2 (by exact_mod_cast loopMeanSum_mul n k)
    rw [hR]
    field_simp [hnR]

/-- The loop count paired against its conditional mean is the mean-square
sum: `⟪n_loop, m⟫ = msqSum c / m0sum c`.  The conditional second moment of
`n_loop` about zero equals mean-square plus variance, so this is the
mean-square part of `nsum c / m0sum c`. -/
theorem inner_obsL_obsM (c : ℕ) : ⟪obsL c, obsM c⟫ = msqSum c / m0sum c := by
  rw [inner_apply]
  refine (expect_eq_product_sum c (fun n k j _t => (j : ℝ) * ((k : ℝ) / n))).trans ?_
  have hcell : ∀ n k : ℕ,
      (∑ j ∈ Finset.range (k + 1), ∑ _t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * ((j : ℝ) * ((k : ℝ) / n)))
      = ((c + 1 : ℕ) : ℝ) *
          (((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n k
    rw [sum_jt c n k (fun j => (j : ℝ) * ((k : ℝ) / n))]
    congr 1
    have hcomm : ∀ j : ℕ,
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * ((j : ℝ) * ((k : ℝ) / n))
          = ((k : ℝ) / n) * ((cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (j : ℝ)) :=
      fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hcomm j), ← Finset.mul_sum, sum_loop_mean_cell,
      ← mul_div_assoc, msq_cell_id]
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => hcell n k))]
  simp_rw [← Finset.mul_sum]
  rw [← msqSum.eq_def, censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-- The squared norm of the conditional mean: `‖m‖² = msqSum c / m0sum c`. -/
theorem norm_sq_obsM (c : ℕ) : ‖obsM c‖ ^ 2 = msqSum c / m0sum c := by
  rw [← real_inner_self_eq_norm_sq, inner_apply]
  refine (expect_eq_product_sum c (fun n k _j _t =>
      ((k : ℝ) / n) * ((k : ℝ) / n))).trans ?_
  have hcell : ∀ n k : ℕ,
      (∑ j ∈ Finset.range (k + 1), ∑ _t ∈ Finset.range (c + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * (((k : ℝ) / n) * ((k : ℝ) / n)))
      = ((c + 1 : ℕ) : ℝ) *
          (((k : ℝ) / n) ^ 2 * (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ))) := by
    intro n k
    rw [sum_jt c n k (fun _ => ((k : ℝ) / n) * ((k : ℝ) / n))]
    congr 1
    rw [← Finset.sum_mul]
    have hm : (∑ j ∈ Finset.range (k + 1),
        (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)))
        = (n : ℝ) ^ (2 * k) / ((n ! : ℝ) * (k ! : ℝ)) := by
      rw [← Finset.sum_div, ← Nat.cast_sum, margin_count, Nat.cast_pow]
    rw [hm]
    ring
  rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun k _ => hcell n k))]
  simp_rw [← Finset.mul_sum]
  rw [← msqSum.eq_def, censusM0_cast]
  have hc1 : (0 : ℝ) < ((c + 1 : ℕ) : ℝ) := by positivity
  rw [mul_div_mul_left _ _ hc1.ne']

/-!
## Section 3: the variance separation
-/

/-- The projections of the loop count and of its conditional mean onto the
count span agree: the difference `n_loop − m` is orthogonal to the span, and
`m − proj(m)` is too, so `n_loop − proj(m)` exhibits `proj(m)` as the
projection of `n_loop`. -/
theorem starProjection_obsL_eq_coe (c : ℕ) :
    ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsL c) : L2fun c)
      = ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c) := by
  have hmem : (((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c)) : L2fun c)
      ∈ countSpan (obsV c) (obsE c) (obsT c) :=
    (countSpan (obsV c) (obsE c) (obsT c)).starProjection_apply_mem _
  have hz : obsL c
      - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c)
      ∈ (countSpan (obsV c) (obsE c) (obsT c))ᗮ := by
    have h1 : obsL c - obsM c ∈ (countSpan (obsV c) (obsE c) (obsT c))ᗮ :=
      obsL_sub_obsM_mem_orthogonal c
    have h2 : obsM c
        - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c)
        ∈ (countSpan (obsV c) (obsE c) (obsT c))ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal _
    have hsum := (countSpan (obsV c) (obsE c) (obsT c))ᗮ.add_mem h1 h2
    have heq : obsL c - obsM c
        + (obsM c
          - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c))
        = obsL c
          - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c) :=
      by abel
    rw [heq] at hsum
    exact hsum
  exact Submodule.eq_starProjection_of_mem_orthogonal' hmem hz (by abel)

/-- The residual of the loop count splits: `r(n_loop) = (n_loop − m) + r(m)`. -/
theorem resid_obsL_eq (c : ℕ) :
    Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsL c)
      = (obsL c - obsM c)
        + Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c) := by
  unfold Gap2AnomalyAsymptotics.resid
  rw [starProjection_obsL_eq_coe]
  abel

/-- **The variance separation (TARGET 2).**  The squared residual norm of
the loop count against the count span splits into the conditional-variance
piece and the mean-residual piece:
`‖r(n_loop)‖² = ‖n_loop − m‖² + ‖r(m)‖²`.  The two pieces are orthogonal:
`n_loop − m` is orthogonal to the whole span (hence to `proj(m)`), and its
inner product with `m` is `⟪n_loop, m⟫ − ‖m‖² = 0`. -/
theorem norm_sq_resid_obsL (c : ℕ) :
    ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsL c)‖ ^ 2
      = ‖obsL c - obsM c‖ ^ 2
        + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2 := by
  rw [resid_obsL_eq]
  simp only [pow_two]
  apply norm_add_sq_eq_norm_sq_add_norm_sq_real
  unfold Gap2AnomalyAsymptotics.resid
  rw [inner_sub_right]
  have h1 : ⟪obsL c - obsM c, obsM c⟫ = 0 := by
    rw [inner_sub_left, inner_obsL_obsM, real_inner_self_eq_norm_sq, norm_sq_obsM,
      sub_self]
  have h2 : ⟪obsL c - obsM c,
      ((countSpan (obsV c) (obsE c) (obsT c)).starProjection (obsM c) : L2fun c)⟫
      = 0 := by
    have hmem := (countSpan (obsV c) (obsE c) (obsT c)).starProjection_apply_mem (obsM c)
    have ho := (Submodule.mem_orthogonal _ _).1 (obsL_sub_obsM_mem_orthogonal c) _ hmem
    rw [real_inner_comm] at ho
    exact ho
  rw [h1, h2, sub_self]

/-- The conditional-variance sum `nvarSum c = nsum c − msqSum c`: the census
numerator of `E_μ[Var(n_loop ∣ n,k)]`, the evaluated variance piece of the
residual.  (Per cell this is `k(n−1)n^(2k−2)` for `n ≥ 1`, the binomial
variance `k·(1/n)·(1 − 1/n)` times the cell mass `n^(2k)`.) -/
noncomputable def nvarSum (c : ℕ) : ℝ := nsum c - msqSum c

/-- The centered loop count's squared norm is the variance sum:
`‖n_loop − m‖² = E_μ[Var(n_loop ∣ n,k)] = (nsum c − msqSum c)/m0sum c`. -/
theorem norm_sq_sub_obsM (c : ℕ) :
    ‖obsL c - obsM c‖ ^ 2 = nvarSum c / m0sum c := by
  have h : ‖obsL c - obsM c‖ ^ 2 = ⟪obsL c - obsM c, obsL c - obsM c⟫ :=
    (real_inner_self_eq_norm_sq _).symm
  rw [h, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq (obsL c), norm_sq_nloop,
    real_inner_self_eq_norm_sq (obsM c), norm_sq_obsM,
    real_inner_comm (obsL c) (obsM c), inner_obsL_obsM, nvarSum.eq_def]
  ring

/-- The variance sum is nonnegative: it is the squared norm of the centered
loop count times the positive normalization.  (The kernel verifies that
`nsum c ≥ msqSum c`, the census Cauchy–Schwarz inequality on the loop
count.) -/
theorem nvarSum_nonneg (c : ℕ) : 0 ≤ nvarSum c := by
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have h := norm_sq_sub_obsM c
  rw [← div_mul_cancel₀ (nvarSum c) hm0.ne', ← h]
  exact mul_nonneg (sq_nonneg _) hm0.le

/-- qfrac as the residual ratio of the loop count: the equality half of the
A49 `qfrac_le_mechanismBound`. -/
theorem qfrac_eq_resid_ratio (c : ℕ) :
    qfrac c = ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsL c)‖ ^ 2
      / ‖obsP c‖ ^ 2 :=
  Gap2AnomalyAsymptotics.anomaly_fraction_eq (obsV c) (obsE c) (obsT c) (obsL c) (obsP c)
    (hObs c) (nproper_eq_sub c) rfl

/-- **qfrac as an evaluated ratio (TARGET 2).**  The A49 bound
`q(c) ≤ mechanismBound c` becomes the identity
`q(c) = (nvarSum c + ‖r(m)‖²·m0sum c) / dsum c`:
the variance piece and the mean-residual piece, each exact, over the proper
second moment.  What remains for the sharp rate is the asymptotic evaluation
of the two pieces: `nvarSum c / dsum c ~ (log c)/(2c²)` and
`‖r(m)‖²·m0sum c / dsum c = o((log c)/c²)`. -/
theorem qfrac_eval (c : ℕ) (hc : 2 ≤ c) :
    qfrac c
      = (nvarSum c
          + ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (obsM c)‖ ^ 2 * m0sum c)
        / dsum c := by
  rw [qfrac_eq_resid_ratio c, norm_sq_resid_obsL, norm_sq_sub_obsM, norm_sq_nproper]
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hd : (0 : ℝ) < dsum c := dsum_pos c hc
  field_simp [hm0.ne', hd.ne']

/-- The residual is the minimal-distance element to the span: any explicit
span element gives a one-sided bound.  This is the workhorse for bounding
`‖r(m)‖²` with test functions `a·nE + b·nV`. -/
theorem norm_sq_resid_le_of_mem_span (c : ℕ) (x y : L2fun c)
    (hy : y ∈ countSpan (obsV c) (obsE c) (obsT c)) :
    ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  unfold Gap2AnomalyAsymptotics.resid
  have hdecomp : x - y
      = (x - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection x : L2fun c))
        + (((countSpan (obsV c) (obsE c) (obsT c)).starProjection x : L2fun c) - y) := by
    abel
  rw [hdecomp]
  have horth : ⟪x
        - ((countSpan (obsV c) (obsE c) (obsT c)).starProjection x : L2fun c),
        ((countSpan (obsV c) (obsE c) (obsT c)).starProjection x : L2fun c) - y⟫ = 0 := by
    have hmem : ((countSpan (obsV c) (obsE c) (obsT c)).starProjection x : L2fun c) - y
        ∈ countSpan (obsV c) (obsE c) (obsT c) :=
      (countSpan (obsV c) (obsE c) (obsT c)).sub_mem
        ((countSpan (obsV c) (obsE c) (obsT c)).starProjection_apply_mem x) hy
    have ho := (Submodule.mem_orthogonal _ _).1
      (Submodule.sub_starProjection_mem_orthogonal x) _ hmem
    rw [real_inner_comm] at ho
    exact ho
  simp only [pow_two]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_real horth]
  exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))

#print axioms sum_centered_cell
#print axioms obsL_sub_obsM_mem_orthogonal
#print axioms inner_obsL_obsM
#print axioms norm_sq_obsM
#print axioms norm_sq_resid_obsL
#print axioms norm_sq_sub_obsM
#print axioms nvarSum_nonneg
#print axioms qfrac_eq_resid_ratio
#print axioms qfrac_eval
#print axioms norm_sq_resid_le_of_mem_span

end Gap2CensusVarianceSep
