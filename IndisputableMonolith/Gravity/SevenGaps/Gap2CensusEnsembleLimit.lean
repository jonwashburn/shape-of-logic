import IndisputableMonolith.Gravity.SevenGaps.Gap2CensusMeasure
import IndisputableMonolith.Gravity.SevenGaps.Gap2AnomalyAsymptotics

/-!
# Gap 2 / C11 / A49: the anomaly fraction at the census measure, and `q(c) → 0`

The A48 arc closed `mechanismBound c → 0` at kernel strength, and the
companion module `Gap2CensusMeasure` proved the product-form census law:
expectations under the census measure `μ_c` are the product-form weighted
sums, with the two second moments `E_μ[n_loop²] = nsum c / m0sum c` and
`E_μ[n_proper²] = dsum c / m0sum c` whose ratio is `mechanismBound c`.

This module instantiates the anomaly algebra of `Gap2AnomalyAsymptotics`
at the census measure and composes the three pieces into the ensemble
statement of the C11 fork:

* `L2fun c`: the space of class functions `Ensemble c → ℝ`, as a separate
  type so that the `L²(μ_c)` structures declared here are the only ones
  typeclass resolution sees on it.
* `μcore`: the `L²(μ_c)` inner-product core, `⟪f, g⟫ = Σ_x μ_c(x)·f(x)·g(x)`.
  The inner product is definite because every class carries positive
  probability (`μprob_pos`).
* `norm_sq_nloop`, `norm_sq_nproper`: the `L²` norms of the loop and
  proper-edge observables are the product-form moment sums.
* `qfrac`: the anomaly fraction `q(c) = ‖r(h)‖² / ‖h‖²` of the incidence
  history `h = 2·n_proper` against the count span `{nV, nE, nT}`, the
  quantity C11 measured on the enumerated ensemble at caps 1 to 6.
* `qfrac_le_mechanismBound`: `q(c) ≤ mechanismBound c` for `c ≥ 2`, the
  composition of the anomaly moment bound (`anomaly_fraction_le`, the
  contraction `‖r(n_loop)‖² ≤ ‖n_loop‖²`) with the census moment
  identities and the cancelled normalization.
* `qfrac_tendsto_zero`: **`q(c) → 0`**, the ensemble statement of the C11
  fork, by squeeze against `tendsto_mechanismBound_zero` (A48).

All results audit to the base triple `[propext, Classical.choice,
Quot.sound]` (`#print axioms` at the end of the file).  Classical choice
enters through the enumeration of the finite orbit space, the projection
onto the count span, and the real analysis of the squeeze.
-/

open scoped RealInnerProductSpace
open Gap2CensusProductForm Gap2M0Asymptotics Gap2CensusMeasure
open Filter Topology

namespace Gap2CensusEnsembleLimit

/-- The space of class functions on the cap-`c` ensemble, as a separate
type.  Keeping this distinct from the raw function type means the
`L²(μ_c)` normed and inner-product structures declared below are the only
ones typeclass resolution ever finds on it (the sup-norm structures on raw
function types would otherwise compete with the census inner product). -/
def L2fun (c : ℕ) : Type := Ensemble c → ℝ

noncomputable instance (c : ℕ) : AddCommGroup (L2fun c) := Pi.addCommGroup

noncomputable instance (c : ℕ) : Module ℝ (L2fun c) :=
  Pi.module (Ensemble c) (fun _ => ℝ) ℝ

/-- The ensemble is nonempty: the `(0, 0, 0)` cell contains the empty edge
sequence. -/
instance ensembleNonempty (c : ℕ) : Nonempty (Ensemble c) :=
  ⟨⟨⟨0, Nat.zero_lt_succ c⟩, ⟨0, Nat.zero_lt_succ c⟩, ⟨0, Nat.zero_lt_succ 0⟩,
      ⟨0, Nat.zero_lt_succ c⟩, ⟦⟨isEmptyElim, by simp [loopCount, loopSet]⟩⟧⟩⟩

/-- Class functions form a nontrivial space (the zero function differs from
the constant-one function, since the ensemble is nonempty); needed for the
normed-space structure of `L²(μ_c)`. -/
noncomputable instance (c : ℕ) : Nontrivial (L2fun c) :=
  ⟨0, (fun _ => 1 : L2fun c), fun h => by
    obtain ⟨x⟩ := ensembleNonempty c
    have h1 : (0 : ℝ) = 1 := congrFun h x
    exact zero_ne_one h1⟩

/-- The `L²(μ_c)` inner-product core on class functions:
`⟪f, g⟫ = Σ_x μ_c(x)·f(x)·g(x)`.  Definite because the census law gives
every isomorphism class positive probability, so `⟪f, f⟫ = 0` forces `f` to
vanish at every class. -/
noncomputable instance μcore (c : ℕ) : InnerProductSpace.Core ℝ (L2fun c) where
  inner f g := ∑ x : Ensemble c, μprob c x * (f x * g x)
  conj_inner_symm x y := by
    show (∑ i : Ensemble c, μprob c i * (y i * x i))
        = ∑ i : Ensemble c, μprob c i * (x i * y i)
    exact Finset.sum_congr rfl fun i _ => by ring
  re_inner_nonneg x := by
    show (0 : ℝ) ≤ ∑ i : Ensemble c, μprob c i * (x i * x i)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (μprob_pos c i).le (mul_self_nonneg _)
  add_left x y z := by
    show (∑ i : Ensemble c, μprob c i * ((x i + y i) * z i))
        = (∑ i : Ensemble c, μprob c i * (x i * z i))
          + ∑ i : Ensemble c, μprob c i * (y i * z i)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  smul_left x y r := by
    show (∑ i : Ensemble c, μprob c i * ((r • x i) * y i))
        = r * ∑ i : Ensemble c, μprob c i * (x i * y i)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring
  definite x (hx : (∑ i : Ensemble c, μprob c i * (x i * x i)) = 0) := by
    have h0 : ∀ i ∈ (Finset.univ : Finset (Ensemble c)), 0 ≤ μprob c i * (x i * x i) :=
      fun i _ => mul_nonneg (μprob_pos c i).le (mul_self_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg h0).1 hx
    funext i
    have hi := hz i (Finset.mem_univ i)
    rcases mul_eq_zero.1 hi with hμ | hx2
    · exact absurd hμ (μprob_pos c i).ne'
    · exact mul_self_eq_zero.1 hx2

/-- The normed group structure on class functions induced by the `L²(μ_c)`
inner product. -/
noncomputable instance μNorm (c : ℕ) : NormedAddCommGroup (L2fun c) :=
  @InnerProductSpace.Core.toNormedAddCommGroup _ _ _ _ _ (μcore c)

/-- The `L²(μ_c)` inner-product space on class functions. -/
noncomputable instance μIPS (c : ℕ) : InnerProductSpace ℝ (L2fun c) :=
  InnerProductSpace.ofCore _

/-- The inner product unfolds to the `μ_c`-weighted sum. -/
theorem inner_apply (c : ℕ) (f g : L2fun c) :
    ⟪f, g⟫ = ∑ x : Ensemble c, μprob c x * (f x * g x) := rfl

/-- The squared `L²(μ_c)` norm is the second census moment of the function. -/
theorem norm_sq_apply (c : ℕ) (f : L2fun c) :
    ‖f‖ ^ 2 = ∑ x : Ensemble c, μprob c x * (f x * f x) := by
  rw [← real_inner_self_eq_norm_sq f, inner_apply]

/-- The vertex-count observable as an element of `L²(μ_c)`. -/
def obsV (c : ℕ) : L2fun c := nV (c := c)

/-- The edge-count observable as an element of `L²(μ_c)`. -/
def obsE (c : ℕ) : L2fun c := nE (c := c)

/-- The tet-count observable as an element of `L²(μ_c)`. -/
def obsT (c : ℕ) : L2fun c := nT (c := c)

/-- The loop-count observable as an element of `L²(μ_c)`. -/
def obsL (c : ℕ) : L2fun c := nloop (c := c)

/-- The proper-edge count observable as an element of `L²(μ_c)`. -/
def obsP (c : ℕ) : L2fun c := nproper (c := c)

/-- `n_proper = nE − n_loop` as class functions: on the ensemble the loop
count never exceeds the edge count, so the natural subtraction casts to
real subtraction. -/
theorem nproper_eq_sub (c : ℕ) : obsP c = obsE c - obsL c := by
  funext x
  show ((x.2.1.1 - x.2.2.1.1 : ℕ) : ℝ) = (x.2.1.1 : ℝ) - (x.2.2.1.1 : ℝ)
  exact Nat.cast_sub (Nat.lt_succ_iff.mp x.2.2.1.2)

/-- The squared `L²(μ_c)` norm of the loop count is the product-form sum:
`‖n_loop‖² = E_μ[n_loop²] = nsum c / m0sum c`. -/
theorem norm_sq_nloop (c : ℕ) :
    ‖obsL c‖ ^ 2 = nsum c / m0sum c := by
  refine (norm_sq_apply c (obsL c)).trans ?_
  show (∑ x : Ensemble c, μprob c x * (nloop x * nloop x)) = nsum c / m0sum c
  rw [← expect_nloop_sq c]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The squared `L²(μ_c)` norm of the proper-edge count:
`‖n_proper‖² = E_μ[n_proper²] = dsum c / m0sum c`. -/
theorem norm_sq_nproper (c : ℕ) :
    ‖obsP c‖ ^ 2 = dsum c / m0sum c := by
  refine (norm_sq_apply c (obsP c)).trans ?_
  show (∑ x : Ensemble c, μprob c x * (nproper x * nproper x)) = dsum c / m0sum c
  rw [← expect_nproper_sq c]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- At caps `c ≥ 2` the proper-edge observable is not the zero function:
its squared norm `dsum c / m0sum c` is strictly positive. -/
theorem nproper_ne_zero (c : ℕ) (hc : 2 ≤ c) : obsP c ≠ 0 := by
  intro hz
  have hpos : (0 : ℝ) < dsum c / m0sum c := div_pos (dsum_pos c hc) (m0sum_pos c)
  rw [← norm_sq_nproper c] at hpos
  rw [hz] at hpos
  simp at hpos

/-- The history observable `h = 2·n_proper`, the C11 incidence history as a
class function in `L²(μ_c)`. -/
noncomputable def hObs (c : ℕ) : L2fun c := (2 : ℝ) • obsP c

/-- **The C11 anomaly fraction of the cap-`c` census ensemble.**
`q(c) = ‖r(h)‖² / ‖h‖²`: the squared norm of the residual of the incidence
history `h = 2·n_proper` against the count span `{nV, nE, nT}`, over the
squared norm of `h`, in `L²(μ_c)`.  This is the quantity the A36
computation measured on the enumerated ensemble at caps 1 to 6. -/
noncomputable def qfrac (c : ℕ) : ℝ :=
  ‖Gap2AnomalyAsymptotics.resid (obsV c) (obsE c) (obsT c) (hObs c)‖ ^ 2 / ‖hObs c‖ ^ 2

/-- The anomaly fraction is a ratio of squares, hence nonnegative at every
cap. -/
theorem qfrac_nonneg (c : ℕ) : 0 ≤ qfrac c :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- **The anomaly fraction is bounded by the mechanism bound:**
`q(c) ≤ mechanismBound c` for `c ≥ 2`.  The anomaly algebra contracts the
residual (`q ≤ ‖n_loop‖² / ‖n_proper‖²`), the census law evaluates the two
norms as `nsum c / m0sum c` and `dsum c / m0sum c`, and the shared
normalization cancels to `nsum c / dsum c = mechanismBound c`. -/
theorem qfrac_le_mechanismBound (c : ℕ) (hc : 2 ≤ c) :
    qfrac c ≤ mechanismBound c := by
  have hle := Gap2AnomalyAsymptotics.anomaly_fraction_le
    (obsV c) (obsE c) (obsT c) (obsL c) (obsP c) (hObs c)
    (nproper_eq_sub c) rfl (nproper_ne_zero c hc)
  rw [norm_sq_nloop, norm_sq_nproper] at hle
  have hm0 : (0 : ℝ) < m0sum c := m0sum_pos c
  have hd : (0 : ℝ) < dsum c := dsum_pos c hc
  have heq : (nsum c / m0sum c) / (dsum c / m0sum c) = mechanismBound c := by
    show (nsum c / m0sum c) / (dsum c / m0sum c) = nsum c / dsum c
    field_simp [hm0.ne', hd.ne']
  exact heq ▸ hle

/-- **The C11 ensemble limit (the fork closes): `q(c) → 0`.**  The anomaly
fraction of the census ensemble vanishes in the cap limit, squeezed between
`0` and the mechanism bound, whose vanishing is the A48 theorem
`tendsto_mechanismBound_zero`. -/
theorem qfrac_tendsto_zero :
    Filter.Tendsto qfrac Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_mechanismBound_zero ?_ ?_
  · exact Filter.Eventually.of_forall qfrac_nonneg
  · filter_upwards [eventually_ge_atTop 2] with c hc
    exact qfrac_le_mechanismBound c hc

/-- **Explicit decay envelope for `q(c)` (the strongest proved rate).**
Composing `q ≤ B` with the A48 explicit bound on `B`: at caps `c ≥ 9` with
`smallMass c / m0sum c ≤ 1/2`,
`q(c) ≤ 8·(smallMass c / m0sum c) + 1/(√(c·log c) − 1)`.  This is the
banked rate toward the sharp `q(c) = (log c)/(2c²)·(1 + o(1))`: the envelope
decays like `1/√(c·log c)`, one-sided at the `2√(c·log c)` split scale; the
sharp constant needs the two-sided saddle concentration at the true Laplace
scale `n*` (`n* log n* = 2c`), which remains DERIVED-UNFORMALIZED. -/
theorem qfrac_le_explicit (c : ℕ) (hc : 9 ≤ c)
    (hs : smallMass c / m0sum c ≤ 1 / 2) :
    qfrac c ≤ 8 * (smallMass c / m0sum c)
      + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) :=
  le_trans (qfrac_le_mechanismBound c (by omega)) (mechanismBound_le hc hs)

/-- The explicit envelope holds eventually, with no side hypotheses: the
small-mass ratio tends to `0` (A48), so it is eventually at most `1/2`. -/
theorem qfrac_eventually_explicit :
    ∀ᶠ c : ℕ in Filter.atTop,
      qfrac c ≤ 8 * (smallMass c / m0sum c)
        + 1 / (Real.sqrt ((c : ℝ) * Real.log c) - 1) := by
  filter_upwards [eventually_ge_atTop 9,
    tendsto_smallMass_div_m0sum_zero.eventually
      (Iic_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with c hc hs
  exact qfrac_le_explicit c hc hs

#print axioms qfrac_tendsto_zero
#print axioms qfrac_le_mechanismBound
#print axioms qfrac_le_explicit
#print axioms qfrac_eventually_explicit
#print axioms qfrac_nonneg
#print axioms norm_sq_nloop
#print axioms norm_sq_nproper
#print axioms nproper_ne_zero
#print axioms nproper_eq_sub
#print axioms inner_apply
#print axioms norm_sq_apply

end Gap2CensusEnsembleLimit
