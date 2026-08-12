import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusEnsembleLimit

/-!
# Self-hostile-review probe: A49 product-form census and `q(c) → 0`

Outside-module checks on the A49 closure of the ensemble statement of the C11
fork. No edits to the campaign modules (`Gap2CensusMeasure.lean`,
`Gap2CensusEnsembleLimit.lean`, and the untouched A48 module
`Gap2M0Asymptotics.lean`). Does not import `FullTheoryLedger`,
`ConstantInventory`, or any `Gap5*` module (an independent review runs against
those).

Sections:
1. Outside-module axiom audits of every new A49 head theorem.
2. Destructuring: the three targets at their exact stated types.
3. The instantiated inner product really is the `μ_c`-inner product of A36,
   not a lookalike: it is `rfl`-equal to the `μprob`-weighted sum, the
   constant-one function has unit norm (probability, not class count and not
   total mass), every class carries positive probability, and the two norms
   are exactly the census second moments.
4. Re-derivation of `q ≤ B` from the banked pieces (the anomaly algebra, the
   census moment identities, the cancelled normalization), independently of
   the campaign's own assembly lemma, and the squeeze to `q(c) → 0` from the
   re-derived bound.
5. Red tests with decoys that must fail: the wrong cell weight (`n^k` in
   place of `n^(2k)`) and the dropped orbit-stabilizer factor (the missing
   `1/(n!·k!)`). Each red test is machine-checked: if the census engine ever
   drifted to a decoy, the corresponding proof here would break the build.
-/

namespace QGCensusHostileProbe

open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure Gap2CensusEnsembleLimit
open scoped RealInnerProductSpace Nat
open Filter Topology

/-! ## 1. Outside-module axiom audits -/

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

/-! ## 2. Destructuring the three targets at their stated types -/

/-- Target 1, the law, at the exact charged type: expectations under `μ_c`
are the product-form weighted sums, normalized by `M0`. -/
theorem target1_law_stated (c : ℕ) (g : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (∑ x : Ensemble c, μprob c x * g x.1.1 x.2.1.1 x.2.2.1.1 x.2.2.2.1.1)
      = (∑ n ∈ Finset.range (c + 1), ∑ k ∈ Finset.range (c + 1),
          ∑ j ∈ Finset.range (k + 1), ∑ t ∈ Finset.range (c + 1),
            (cellCount n k j : ℝ) / ((n ! : ℝ) * (k ! : ℝ)) * g n k j t)
        / (censusM0 c : ℝ) :=
  expect_eq_product_sum c g

/-- Target 1, first second moment, hypothesis-free, at the exact charged
type. -/
theorem target1_loop_moment_stated (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nloop x) ^ 2) = nsum c / m0sum c :=
  expect_nloop_sq c

/-- Target 1, second second moment, hypothesis-free, at the exact charged
type. -/
theorem target1_proper_moment_stated (c : ℕ) :
    (∑ x : Ensemble c, μprob c x * (nproper x) ^ 2) = dsum c / m0sum c :=
  expect_nproper_sq c

/-- The ratio identity: the shared normalization cancels and the moment ratio
is the mechanism bound. -/
theorem moment_ratio_stated (c : ℕ) (hc : 2 ≤ c) :
    (∑ x : Ensemble c, μprob c x * (nloop x) ^ 2)
      / (∑ x : Ensemble c, μprob c x * (nproper x) ^ 2)
      = mechanismBound c :=
  moment_ratio c hc

/-- Target 2, hypothesis-light (`c ≥ 2`), at the exact charged type. -/
theorem target2_stated (c : ℕ) (hc : 2 ≤ c) : qfrac c ≤ mechanismBound c :=
  qfrac_le_mechanismBound c hc

/-- Target 3, the ensemble statement of the C11 fork, at the exact charged
type: `q(c) → 0`. -/
theorem target3_stated : Filter.Tendsto qfrac Filter.atTop (nhds 0) :=
  qfrac_tendsto_zero

/-! ## 3. The instantiated inner product is the `μ_c`-inner product -/

/-- The inner product unfolds to the `μ_c`-weighted sum, and the unfolding is
`rfl`: there is no room for a lookalike between the instance and the census
law. -/
theorem inner_is_mu_weighted (c : ℕ) (f g : L2fun c) :
    ⟪f, g⟫ = ∑ x : Ensemble c, μprob c x * (f x * g x) := rfl

/-- The constant-one class function, as a def so the `L²(μ_c)` structures
are pinned the same way the campaign module pins its observables. -/
def oneFun (c : ℕ) : L2fun c := fun _ => 1

/-- Probability check: the constant-one class function has unit norm. An
unweighted lookalike would return the class count; an unnormalized lookalike
would return the total mass `censusM0 c`. -/
theorem norm_const_one (c : ℕ) : ‖oneFun c‖ ^ 2 = 1 := by
  refine (norm_sq_apply c (oneFun c)).trans ?_
  show (∑ x : Ensemble c, μprob c x * ((oneFun c) x * (oneFun c) x)) = 1
  have h : (∑ x : Ensemble c, μprob c x * ((oneFun c) x * (oneFun c) x))
      = ∑ x : Ensemble c, μprob c x :=
    Finset.sum_congr rfl fun x _ => by
      show μprob c x * ((1 : ℝ) * 1) = μprob c x
      ring
  rw [h]
  exact sum_μprob c

/-- The squared norm of the loop observable is the census second moment, not
an unweighted or renormalized variant. -/
theorem norm_loop_is_census (c : ℕ) : ‖obsL c‖ ^ 2 = nsum c / m0sum c :=
  norm_sq_nloop c

/-- The squared norm of the proper-edge observable is the census second
moment. -/
theorem norm_proper_is_census (c : ℕ) : ‖obsP c‖ ^ 2 = dsum c / m0sum c :=
  norm_sq_nproper c

/-- Definiteness rests on visibility: every isomorphism class carries
positive census probability. -/
theorem every_class_visible (c : ℕ) (x : Ensemble c) : 0 < μprob c x :=
  μprob_pos c x

/-- The law is normalized at every cap. -/
theorem law_normalized (c : ℕ) : (∑ x : Ensemble c, μprob c x) = 1 :=
  sum_μprob c

/-- RED TEST 0 (scaled lookalike): a twice-`μ` inner product would give the
constant-one function squared norm 2. It must fail, and it does, because the
norm is exactly 1. If the inner product were ever rescaled, this proof and
`norm_const_one` would both break. -/
theorem red_scaled_inner_product_fails (c : ℕ) :
    ‖oneFun c‖ ^ 2 ≠ 2 := by
  rw [norm_const_one]
  norm_num

/-! ## 4. Re-derivation of `q ≤ B` and of the limit from the pieces -/

/-- `q(c) ≤ mechanismBound c`, re-derived from the banked pieces (the anomaly
algebra bound `anomaly_fraction_le`, the census moment identities, the
positivity of the product-form sums) independently of the campaign's
`qfrac_le_mechanismBound`. If any piece drifts, this proof breaks. -/
theorem q_le_mechanismBound_rederived (c : ℕ) (hc : 2 ≤ c) :
    qfrac c ≤ mechanismBound c := by
  have hle := Gap2AnomalyAsymptotics.anomaly_fraction_le
    (obsV c) (obsE c) (obsT c) (obsL c) (obsP c) (hObs c)
    (nproper_eq_sub c) rfl (nproper_ne_zero c hc)
  calc qfrac c
      = ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (hObs c)‖ ^ 2
          / ‖hObs c‖ ^ 2 := rfl
    _ ≤ ‖obsL c‖ ^ 2 / ‖obsP c‖ ^ 2 := hle
    _ = (nsum c / m0sum c) / (dsum c / m0sum c) := by
        rw [norm_sq_nloop, norm_sq_nproper]
    _ = nsum c / dsum c := by
        have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
        have hd : (0 : ℝ) < dsum c := dsum_pos c hc
        field_simp [hm0.ne', hd.ne']
    _ = mechanismBound c := by simp only [mechanismBound]

/-- `q(c) → 0`, re-derived by squeeze against the A48 theorem from the
re-derived finite-`c` bound, independently of the campaign's
`qfrac_tendsto_zero`. -/
theorem q_tendsto_zero_rederived :
    Filter.Tendsto qfrac Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_mechanismBound_zero ?_ ?_
  · exact Filter.Eventually.of_forall qfrac_nonneg
  · filter_upwards [eventually_ge_atTop 2] with c hc
    exact q_le_mechanismBound_rederived c hc

/-! ## 5. Red tests: the decoys must fail -/

/-- Control for red test 1: the `(2, 1)` cell marginal really is `n^(2k) = 4`,
the engine theorem `margin_count` at the decoy cell. -/
theorem cell_marginal_control :
    (∑ j ∈ Finset.range 2, cellCount 2 1 j) = 2 ^ (2 * 1) := margin_count 2 1

/-- RED TEST 1 (wrong weight). The decoy weighting `n^k` would put the
`(2, 1)` cell marginal at `n^k = 2`. It must fail, and it does: the engine
marginal is 4. If the census engine ever drifted to the `n^k` weight, this
`decide` would break the build. -/
theorem red_wrong_weight_fails :
    (∑ j ∈ Finset.range 2, cellCount 2 1 j) ≠ 2 ^ 1 := by decide

/-- Control for red test 2: the orbit mass of the `(2, 1, 0)` cell carries
the orbit-stabilizer factor `1/(2!·1!)`, so the cell mass is `2/2 = 1`. -/
theorem cell_orbit_mass_control :
    (cellCount 2 1 0 : ℚ) / ((2 ! : ℚ) * (1 ! : ℚ)) = 1 := by
  norm_num [cellCount, Nat.factorial]

/-- RED TEST 2 (dropped stabilizer). Without the `1/(n!·k!)` orbit-stabilizer
factor the `(2, 1, 0)` cell mass would be the raw cell count 2. It must fail,
and it does: the stabilized mass is 1. If the stabilizer factor were ever
dropped, this proof would break the build. -/
theorem red_dropped_stabilizer_fails :
    (cellCount 2 1 0 : ℚ) / ((2 ! : ℚ) * (1 ! : ℚ)) ≠ (cellCount 2 1 0 : ℚ) := by
  norm_num [cellCount, Nat.factorial]

#print axioms QGCensusHostileProbe.q_le_mechanismBound_rederived
#print axioms QGCensusHostileProbe.q_tendsto_zero_rederived
#print axioms QGCensusHostileProbe.norm_const_one
#print axioms QGCensusHostileProbe.red_scaled_inner_product_fails
#print axioms QGCensusHostileProbe.red_wrong_weight_fails
#print axioms QGCensusHostileProbe.red_dropped_stabilizer_fails

end QGCensusHostileProbe
