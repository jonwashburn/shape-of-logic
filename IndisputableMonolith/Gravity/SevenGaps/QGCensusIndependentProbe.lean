import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusEnsembleLimit

/-!
# QGCensusIndependentProbe: the hostile reviewer's own probe (A49 review)

Written by the independent hostile reviewer of the A49 product-form census
campaign (session `qg-census-review`, transcript
`9ffbd7bc-dcca-4f14-b880-a6cb4c40378f`).  This module edits nothing and
imports only the campaign's public surface (`Gap2CensusEnsembleLimit`, which
pulls in `Gap2CensusMeasure`, `Gap2M0Asymptotics`, `Gap2AnomalyAsymptotics`,
and `Gap2CensusProductForm`).  It does not import `FullTheoryLedger`,
`ConstantInventory`, or any `Gap5*` module, and it does not cite the
worker's own probe `QGCensusHostileProbe.lean`: every check here is the
reviewer's own.

Sections:

1. Outside-module axiom audits of all 19 A49 head theorems.
2. Destructuring: the law, the two moments, the probability property, the
   bound, and the limit, restated by the reviewer at their exact charged
   types.
3. The instantiated inner product is the genuine `μ_c`-inner product
   (`rfl`-unfolding, unit norm of the constant-one function, positivity at
   every class), and the observable norms are the census second moments.
4. **Vacuity: `qfrac 2 > 0`, proved from the cap-2 census itself.**  Four
   concrete isomorphism classes (the empty complex at tet label 1, the
   single loop on one vertex, the single proper edge on two vertices, the
   double loop on one vertex) force an inconsistent linear system on any
   purported representation of the incidence history `h = 2·n_proper` as a
   combination of the count observables `{nV, nE, nT}`.  Hence `h` lies
   outside the count span, the residual has strictly positive norm, and the
   anomaly fraction is a strictly positive quantity at cap 2, not a
   definitionally-zero shadow.
5. The reviewer's independent re-derivation of `q(c) ≤ B(c)` and of the
   squeeze `q(c) → 0` from the banked pieces (the anomaly algebra, the
   census moment identities, the A48 limit).
6. The reviewer's own red tests: the dropped-binomial-factor decoy
   (`cellCount` without `C(k, j)`) and the unnormalized-law decoy (the raw
   class mass taken as a probability).  Each is machine-checked to fail.
-/

namespace QGCensusIndependentProbe

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
open scoped Gap2CensusProductForm RealInnerProductSpace Nat
open Filter Topology

/-! ## 1. Outside-module axiom audits of the 19 head theorems -/

#print axioms Gap2CensusMeasure.total_mass
#print axioms Gap2CensusMeasure.expect_eq_product_sum
#print axioms Gap2CensusMeasure.expect_nloop_sq
#print axioms Gap2CensusMeasure.expect_nproper_sq
#print axioms Gap2CensusMeasure.moment_ratio
#print axioms Gap2CensusMeasure.sum_μprob
#print axioms Gap2CensusMeasure.sum_inv_stab_cell
#print axioms Gap2CensusMeasure.μprob_pos
#print axioms Gap2CensusEnsembleLimit.inner_apply
#print axioms Gap2CensusEnsembleLimit.norm_sq_apply
#print axioms Gap2CensusEnsembleLimit.nproper_eq_sub
#print axioms Gap2CensusEnsembleLimit.nproper_ne_zero
#print axioms Gap2CensusEnsembleLimit.norm_sq_nloop
#print axioms Gap2CensusEnsembleLimit.norm_sq_nproper
#print axioms Gap2CensusEnsembleLimit.qfrac_nonneg
#print axioms Gap2CensusEnsembleLimit.qfrac_le_mechanismBound
#print axioms Gap2CensusEnsembleLimit.qfrac_tendsto_zero
#print axioms Gap2CensusEnsembleLimit.qfrac_le_explicit
#print axioms Gap2CensusEnsembleLimit.qfrac_eventually_explicit

/-! ## 2. Destructuring at the exact charged types -/

/-- The law, restated by the reviewer: for EVERY observable `g` of the cell
data `(nV, nE, n_loop, nT)`, the `μ_c`-expectation is the product-form
weighted sum normalized by `M0`.  No restriction on `g`; the
orbit-stabilizer factor `1/(n!·k!)` is present; the normalization is
`censusM0 c`. -/
theorem law_restated (c : ℕ) (g : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ x : Ensemble c, μprob c x * g x.1.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)
      = (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
            (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * g n k j t)
        / (censusM0 c : ℝ) :=
  expect_eq_product_sum c g

/-- The loop second moment at the charged type. -/
theorem loop_moment_restated (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nloop x) ^ 2) = nsum c / m0sum c :=
  expect_nloop_sq c

/-- The proper-edge second moment at the charged type. -/
theorem proper_moment_restated (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nproper x) ^ 2) = dsum c / m0sum c :=
  expect_nproper_sq c

/-- The law is a probability law at every cap (the reviewer's restatement of
`sum_μprob`). -/
theorem law_is_probability (c : ℕ) : (∑ x : Ensemble c, μprob c x) = 1 :=
  sum_μprob c

/-- Every isomorphism class carries positive probability. -/
theorem every_class_positive (c : ℕ) (x : Ensemble c) : 0 < μprob c x :=
  μprob_pos c x

/-- The bound at the charged type. -/
theorem bound_restated (c : ℕ) (hc : 2 ≤ c) : qfrac c ≤ mechanismBound c :=
  qfrac_le_mechanismBound c hc

/-- The ensemble limit at the charged type. -/
theorem limit_restated : Filter.Tendsto qfrac Filter.atTop (nhds 0) :=
  qfrac_tendsto_zero

/-! ## 3. The inner product is the `μ_c`-inner product, not a lookalike -/

/-- The inner product is `rfl`-equal to the `μ_c`-weighted sum: there is no
room for a lookalike between the instance and the census law. -/
theorem inner_is_exactly_mu (c : ℕ) (f g : L2fun c) :
    ⟪f, g⟫ = ∑ x : Ensemble c, μprob c x * (f x * g x) := rfl

/-- The constant-one class function. -/
def constOne (c : ℕ) : L2fun c := fun _ => 1

/-- The constant-one function has unit squared norm: the inner product is
normalized as a probability, not as the class count and not as the total
mass. -/
theorem constOne_norm (c : ℕ) : ‖constOne c‖ ^ 2 = 1 := by
  rw [norm_sq_apply]
  show (∑ x : Ensemble c, μprob c x * ((1 : ℝ) * 1)) = 1
  simp_rw [mul_one]
  exact sum_μprob c

/-- The squared norm of the loop observable is the census second moment. -/
theorem loop_norm_is_census (c : ℕ) : ‖obsL c‖ ^ 2 = nsum c / m0sum c :=
  norm_sq_nloop c

/-- The squared norm of the proper-edge observable is the census second
moment. -/
theorem proper_norm_is_census (c : ℕ) : ‖obsP c‖ ^ 2 = dsum c / m0sum c :=
  norm_sq_nproper c

/-! ## 4. Vacuity: `qfrac 2 > 0`, witnessed by four cap-2 classes -/

/-- Witness class: the empty complex on zero vertices, tet label 1. -/
def ptEmpty1 : Ensemble 2 :=
  ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩,
    ⟦⟨isEmptyElim, by simp [loopCount, loopSet]⟩⟧⟩

/-- Witness class: the single loop on one vertex, tet label 0. -/
def ptLoop : Ensemble 2 :=
  ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟦⟨fun _ => (0, 0), by decide⟩⟧⟩

/-- Witness class: the single proper edge on two vertices, tet label 0. -/
def ptEdge : Ensemble 2 :=
  ⟨⟨2, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟦⟨fun _ => (⟨0, by decide⟩, ⟨1, by decide⟩), by decide⟩⟧⟩

/-- Witness class: the double loop on one vertex, tet label 0. -/
def ptLoop2 : Ensemble 2 :=
  ⟨⟨1, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩, ⟨0, by decide⟩,
    ⟦⟨fun _ => (0, 0), by decide⟩⟧⟩

/-- The observables at the empty complex with tet label 1. -/
theorem obs_at_ptEmpty1 :
    nV ptEmpty1 = 0 ∧ nE ptEmpty1 = 0 ∧ nT ptEmpty1 = 1 ∧ nproper ptEmpty1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num

/-- The observables at the single loop. -/
theorem obs_at_ptLoop :
    nV ptLoop = 1 ∧ nE ptLoop = 1 ∧ nT ptLoop = 0 ∧ nproper ptLoop = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num

/-- The observables at the single proper edge. -/
theorem obs_at_ptEdge :
    nV ptEdge = 2 ∧ nE ptEdge = 1 ∧ nT ptEdge = 0 ∧ nproper ptEdge = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((2 : ℕ) : ℝ) = 2; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((1 : ℕ) : ℝ) = 1; norm_num

/-- The observables at the double loop. -/
theorem obs_at_ptLoop2 :
    nV ptLoop2 = 1 ∧ nE ptLoop2 = 2 ∧ nT ptLoop2 = 0 ∧ nproper ptLoop2 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((1 : ℕ) : ℝ) = 1; norm_num
  · show ((2 : ℕ) : ℝ) = 2; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num
  · show ((0 : ℕ) : ℝ) = 0; norm_num

/-- **The vacuity test: the anomaly fraction is strictly positive at cap
2.**  If the incidence history `h = 2·n_proper` lay in the count span
`{nV, nE, nT}`, its values at the four witness classes would give
`d = 0`, `a + b = 0`, `2a + b = 2`, `a + 2b = 0` simultaneously, which is
inconsistent.  So the residual of `h` is nonzero, its squared norm is
positive, and `qfrac 2` is a genuinely positive quantity. -/
theorem qfrac_two_pos : 0 < qfrac 2 := by
  have hP_ne : obsP 2 ≠ 0 := nproper_ne_zero 2 (le_refl 2)
  have hH_ne : hObs 2 ≠ 0 := by
    show (2 : ℝ) • obsP 2 ≠ 0
    intro hz
    have hscale : obsP 2 = (2 : ℝ)⁻¹ • ((2 : ℝ) • obsP 2) := by
      rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    rw [hz, smul_zero] at hscale
    exact hP_ne hscale
  have hden : (0 : ℝ) < ‖hObs 2‖ ^ 2 := pow_pos (norm_pos_iff.mpr hH_ne) 2
  have hres_ne :
      Gap2AnomalyAsymptotics.resid (obsV 2) (obsE 2) (obsT 2) (hObs 2) ≠ 0 := by
    intro hz
    have hproj : hObs 2 =
        (Gap2AnomalyAsymptotics.countSpan (obsV 2) (obsE 2) (obsT 2)).starProjection
          (hObs 2) := by
      have hz' := hz
      unfold Gap2AnomalyAsymptotics.resid at hz'
      exact sub_eq_zero.1 hz'
    have hmem0 : hObs 2 ∈
        Gap2AnomalyAsymptotics.countSpan (obsV 2) (obsE 2) (obsT 2) := by
      rw [hproj]
      exact (Gap2AnomalyAsymptotics.countSpan (obsV 2) (obsE 2)
        (obsT 2)).starProjection_apply_mem (hObs 2)
    have hmem : hObs 2 ∈ Submodule.span ℝ
        ({obsV 2, obsE 2, obsT 2} : Set (L2fun 2)) := hmem0
    rw [Submodule.mem_span_insert] at hmem
    obtain ⟨a, z1, hz1, hEq⟩ := hmem
    rw [Submodule.mem_span_insert] at hz1
    obtain ⟨b, z2, hz2, hz1eq⟩ := hz1
    rw [Submodule.mem_span_singleton] at hz2
    obtain ⟨d, hz2eq⟩ := hz2
    subst hz2eq
    subst hz1eq
    have eA := congrFun hEq ptEmpty1
    have eB := congrFun hEq ptLoop
    have eC := congrFun hEq ptEdge
    have eD := congrFun hEq ptLoop2
    change (2 : ℝ) • nproper ptEmpty1
        = a • nV ptEmpty1 + (b • nE ptEmpty1 + d • nT ptEmpty1) at eA
    change (2 : ℝ) • nproper ptLoop
        = a • nV ptLoop + (b • nE ptLoop + d • nT ptLoop) at eB
    change (2 : ℝ) • nproper ptEdge
        = a • nV ptEdge + (b • nE ptEdge + d • nT ptEdge) at eC
    change (2 : ℝ) • nproper ptLoop2
        = a • nV ptLoop2 + (b • nE ptLoop2 + d • nT ptLoop2) at eD
    simp only [smul_eq_mul] at eA eB eC eD
    rw [obs_at_ptEmpty1.1, obs_at_ptEmpty1.2.1, obs_at_ptEmpty1.2.2.1,
      obs_at_ptEmpty1.2.2.2] at eA
    rw [obs_at_ptLoop.1, obs_at_ptLoop.2.1, obs_at_ptLoop.2.2.1,
      obs_at_ptLoop.2.2.2] at eB
    rw [obs_at_ptEdge.1, obs_at_ptEdge.2.1, obs_at_ptEdge.2.2.1,
      obs_at_ptEdge.2.2.2] at eC
    rw [obs_at_ptLoop2.1, obs_at_ptLoop2.2.1, obs_at_ptLoop2.2.2.1,
      obs_at_ptLoop2.2.2.2] at eD
    norm_num at eA eB eC eD
    linarith
  have hnum : (0 : ℝ) <
      ‖Gap2AnomalyAsymptotics.resid (obsV 2) (obsE 2) (obsT 2) (hObs 2)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hres_ne) 2
  show (0 : ℝ) <
    ‖Gap2AnomalyAsymptotics.resid (obsV 2) (obsE 2) (obsT 2) (hObs 2)‖ ^ 2 / ‖hObs 2‖ ^ 2
  exact div_pos hnum hden

/-! ## 5. The reviewer's independent re-derivation of the bound and limit -/

/-- `q(c) ≤ B(c)` re-assembled by the reviewer from the banked pieces: the
anomaly algebra contraction (`anomaly_fraction_le`), the two census moment
identities, and the cancelled normalization.  Does not cite the campaign's
`qfrac_le_mechanismBound`. -/
theorem q_le_B_reviewer (c : ℕ) (hc : 2 ≤ c) : qfrac c ≤ mechanismBound c := by
  have hle := Gap2AnomalyAsymptotics.anomaly_fraction_le
    (obsV c) (obsE c) (obsT c) (obsL c) (obsP c) (hObs c)
    (nproper_eq_sub c) rfl (nproper_ne_zero c hc)
  rw [norm_sq_nloop, norm_sq_nproper] at hle
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hd : (0 : ℝ) < dsum c := dsum_pos c hc
  have hcan : (nsum c / m0sum c) / (dsum c / m0sum c) = mechanismBound c := by
    show (nsum c / m0sum c) / (dsum c / m0sum c) = nsum c / dsum c
    field_simp [hm0.ne', hd.ne']
  exact hcan ▸ hle

/-- `q(c) → 0` re-assembled by the reviewer: the squeeze between `0` and the
mechanism bound, whose vanishing is the A48 theorem
`tendsto_mechanismBound_zero`.  Does not cite the campaign's
`qfrac_tendsto_zero`. -/
theorem q_tendsto_zero_reviewer : Filter.Tendsto qfrac Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_mechanismBound_zero ?_ ?_
  · exact Filter.Eventually.of_forall qfrac_nonneg
  · filter_upwards [eventually_ge_atTop 2] with c hc
    exact q_le_B_reviewer c hc

/-! ## 6. The reviewer's own red tests -/

/-- Control for red test A: the `(3, 2, 1)` cell count is
`C(2,1)·3·(9−3) = 36`. -/
theorem dropped_choose_control : cellCount 3 2 1 = 36 := by decide

/-- RED TEST A (dropped binomial factor).  The decoy cell count without the
`C(k, j)` factor would be `3·6 = 18`.  It must fail, and it does: the
kernel-checked count is 36.  If the binomial factor were ever dropped from
the census engine, this `decide` breaks the build. -/
theorem red_dropped_choose_fails :
    cellCount 3 2 1 ≠ 3 ^ 1 * (3 ^ 2 - 3) ^ (2 - 1) := by decide

/-- The raw class mass at cap 2 is `30`, computed from the closed form of
`censusM0`. -/
theorem censusM0_two_val : censusM0 2 = 30 := by
  norm_num [censusM0, Finset.sum_range_succ]

/-- RED TEST B (unnormalized law).  If `μ` were the raw class mass without
the `M0` division, the total at cap 2 would be `30`, not `1`.  It must
fail as a probability, and it does: the raw mass is not normalized.  If the
normalization were ever dropped from the census law, this proof breaks the
build. -/
theorem red_unnormalized_law_fails :
    (∑ x : Ensemble 2, (classMass x : ℝ)) ≠ 1 := by
  have hsum : (∑ x : Ensemble 2, (classMass x : ℝ)) = (censusM0 2 : ℝ) := by
    exact_mod_cast total_mass 2
  rw [hsum, censusM0_two_val]
  norm_num

#print axioms QGCensusIndependentProbe.qfrac_two_pos
#print axioms QGCensusIndependentProbe.q_le_B_reviewer
#print axioms QGCensusIndependentProbe.q_tendsto_zero_reviewer
#print axioms QGCensusIndependentProbe.inner_is_exactly_mu
#print axioms QGCensusIndependentProbe.constOne_norm
#print axioms QGCensusIndependentProbe.red_dropped_choose_fails
#print axioms QGCensusIndependentProbe.red_unnormalized_law_fails

end QGCensusIndependentProbe
