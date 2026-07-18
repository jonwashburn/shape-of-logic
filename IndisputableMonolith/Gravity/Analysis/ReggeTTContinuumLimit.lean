import IndisputableMonolith.Gravity.Analysis.ReggeTTBlochAssembly

/-!
# Regge TT cosine two-jet continuum limit

This module is the C-DAG2 continuum stage.  It imports the finite Bloch
assembly and no continuum-certificate spike.  Exact Bloch orthogonality has
already removed the cell sum, so the proof is a local cosine two-jet limit of
the finite raw bucket fold.

The reusable theorem `rawCosineFold_scale_tendsto` treats a free real scale
`q`.  Its phase is literally `q * sum_i x_i * (u_i / 2)`, preserving the
doubled-midpoint convention.  The constant term is removed by the assembled
zero-mode theorem, and the local centered-second-difference bridge supplies
the cosine second jet.  The final theorem composes this result with
`q_N = 2*pi/N`, the eventual finite assembly theorem, and the exact
`momentumNormSq` normalization.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTContinuumLimit

open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit
open ReggeTTBlochAssembly
open ReggeTTHingeAwareZeroMode

noncomputable section

/-- Literal midpoint-displacement phase `sum_i x_i * (u_i / 2)`. -/
def rawPhaseLinear (x : Fin 3 → ℝ) (b : Bucket) : ℝ :=
  ∑ i : Fin 3, x i * (((b.phase i : ℤ) : ℝ) / 2)

/-- Frozen phase quadratic, with the literal doubled-key normalization
`(sum_i x_i * (u_i / 2))^2`. -/
def rawPhaseQuadratic (x : Fin 3 → ℝ) (b : Bucket) : ℝ :=
  rawPhaseLinear x b ^ (2 : ℕ)

/-- Raw cosine evaluator at a free continuous momentum scale `q`. -/
def rawCosineEvaluatorAtScale (q : ℝ) (x : Fin 3 → ℝ) (b : Bucket) : ℝ :=
  Real.cos (q * rawPhaseLinear x b)

/-- The finite raw bucket fold at continuous scale `q`. -/
def rawCosineFoldAtScale (q : ℝ) (x : Fin 3 → ℝ)
    (E : Fin 3 → Fin 3 → ℝ) : ℝ :=
  reggeTTBlochFold rawCosineSupport (rawCosineEvaluatorAtScale q x)
    (rawBucketAmplitude E)

/-- Squared Euclidean norm of a real mode direction. -/
def realModeNormSq (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, x i ^ (2 : ℕ)

/-- Real direction of an integer mode, normalized to unit Euclidean norm. -/
def normalizedRealMode (m : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun i => (m i : ℝ) / Real.sqrt (realModeNormSq (fun j => (m j : ℝ)))

/-- The continuous scale used by the side-`N` commensurate momentum. -/
def sideScale (N : ℕ) : ℝ :=
  2 * Real.pi / (N : ℝ)

/-- The scale-zero raw cosine fold is the assembled constant block and hence
vanishes.  This consumes the hinge-aware assembled zero-mode theorem, not a
stencil-only cancellation. -/
theorem rawCosineFoldAtScale_zero (x : Fin 3 → ℝ)
    (E : Fin 3 → Fin 3 → ℝ) :
    rawCosineFoldAtScale 0 x E = 0 := by
  have hfold :=
    rawCosineFold_eq_rawTripleSum (N := 1) E (fun _ => (0 : ℤ))
  have heval :
      rawCosineFoldAtScale 0 x E =
        reggeTTBlochFold rawCosineSupport
          (@rawCosineEvaluator 1 (by infer_instance) (fun _ => (0 : ℤ)))
          (rawBucketAmplitude E) := by
    unfold rawCosineFoldAtScale reggeTTBlochFold
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [rawCosineEvaluatorAtScale, rawPhaseLinear, rawCosineEvaluator,
      commensurateMomentum]
  rw [heval, hfold]
  have hone : ∀ p : Fin 6 × Fin 6 × Fin 6,
      rawCosineEvaluator 1 (fun _ => (0 : ℤ)) (bucketKeyOf p) = 1 := by
    intro p
    unfold rawCosineEvaluator commensurateMomentum
    norm_num
  have hsum :
      (∑ p : Fin 6 × Fin 6 × Fin 6,
        rawCosineEvaluator 1 (fun _ => (0 : ℤ)) (bucketKeyOf p) *
          rawTripleWeight E p) = assembledConstantBlock E := by
    unfold assembledConstantBlock rawTripleWeight
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, hone, one_mul, Finset.sum_neg_distrib]
  rw [hsum]
  exact assembledConstantBlock_eq_zero E

/-- The second derivative at zero of `q ↦ cos(aq)` is `-a^2`. -/
theorem iteratedDeriv_two_cos_mul (a : ℝ) :
    iteratedDeriv 2 (fun q : ℝ => Real.cos (a * q)) 0 = -(a ^ (2 : ℕ)) := by
  have hinner : ∀ q : ℝ, HasDerivAt (fun s : ℝ => a * s) a q := by
    intro q
    simpa using (hasDerivAt_id q).const_mul a
  have hfirst :
      deriv (fun q : ℝ => Real.cos (a * q)) =
        fun q : ℝ => -Real.sin (a * q) * a := by
    funext q
    exact ((Real.hasDerivAt_cos (a * q)).comp q (hinner q)).deriv
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  have hsecond :
      HasDerivAt (fun q : ℝ => -Real.sin (a * q) * a)
        (-Real.cos (a * 0) * a * a) 0 := by
    have h :=
      ((Real.hasDerivAt_sin (a * 0)).comp 0 (hinner 0)).neg.mul_const a
    simpa [Function.comp, neg_mul] using h
  rw [hsecond.deriv]
  simp [Real.cos_zero]
  ring

/-- Local cosine two-jet obtained from the reusable centered-second-difference
theorem of the finite-symbol existence stage. -/
theorem cos_sub_one_div_sq_tendsto (a : ℝ) :
    Filter.Tendsto
      (fun q : ℝ => (Real.cos (q * a) - 1) / q ^ (2 : ℕ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-(a ^ (2 : ℕ)) / 2)) := by
  have hC2 : ContDiffAt ℝ 2 (fun q : ℝ => Real.cos (a * q)) 0 :=
    (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hcenter :=
    ReggeTTLocalSymbolExistence.tendsto_centeredSecondDifference_of_contDiffAt
      (fun q : ℝ => Real.cos (a * q)) hC2
  rw [iteratedDeriv_two_cos_mul a] at hcenter
  have hhalf := hcenter.const_mul (1 / 2 : ℝ)
  have heq :
      (fun q : ℝ => (Real.cos (q * a) - 1) / q ^ (2 : ℕ)) =
        fun t : ℝ =>
          1 / 2 *
            (((fun q : ℝ => Real.cos (a * q)) t -
                2 * (fun q : ℝ => Real.cos (a * q)) 0 +
                (fun q : ℝ => Real.cos (a * q)) (-t)) / t ^ (2 : ℕ)) := by
    funext t
    simp only [mul_zero, Real.cos_zero, mul_neg, Real.cos_neg, mul_comm t a]
    ring
  rw [heq, show -(a ^ (2 : ℕ)) / 2 = 1 / 2 * -(a ^ (2 : ℕ)) by ring]
  exact hhalf

/-- REUSABLE CONTINUOUS-VARIABLE HEADLINE: after assembled zero-mode
cancellation, the finite raw cosine fold divided by `q^2` tends exactly to
`reggeTTMoment` with the literal midpoint phase quadratic. -/
theorem rawCosineFold_scale_tendsto (x : Fin 3 → ℝ)
    (E : Fin 3 → Fin 3 → ℝ) :
    Filter.Tendsto
      (fun q : ℝ => rawCosineFoldAtScale q x E / q ^ (2 : ℕ))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (reggeTTMoment rawCosineSupport (rawPhaseQuadratic x)
          (rawBucketAmplitude E))) := by
  have hzero := rawCosineFoldAtScale_zero x E
  have hsum :
      Filter.Tendsto
        (fun q : ℝ =>
          ∑ b ∈ rawCosineSupport,
            ((Real.cos (q * rawPhaseLinear x b) - 1) / q ^ (2 : ℕ)) *
              rawBucketAmplitude E b)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ)
        (nhds
          (∑ b ∈ rawCosineSupport,
            (-(rawPhaseLinear x b ^ (2 : ℕ)) / 2) *
              rawBucketAmplitude E b)) := by
    apply tendsto_finset_sum
    intro b _
    exact (cos_sub_one_div_sq_tendsto (rawPhaseLinear x b)).mul_const
      (rawBucketAmplitude E b)
  have hcongr :
      (fun q : ℝ => rawCosineFoldAtScale q x E / q ^ (2 : ℕ)) =ᶠ[
        nhdsWithin 0 {(0 : ℝ)}ᶜ]
      (fun q : ℝ =>
        ∑ b ∈ rawCosineSupport,
          ((Real.cos (q * rawPhaseLinear x b) - 1) / q ^ (2 : ℕ)) *
            rawBucketAmplitude E b) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    unfold rawCosineFoldAtScale reggeTTBlochFold
    have hzero' :
        ∑ b ∈ rawCosineSupport, rawBucketAmplitude E b = 0 := by
      simpa [rawCosineFoldAtScale, reggeTTBlochFold,
        rawCosineEvaluatorAtScale] using hzero
    calc
      (∑ b ∈ rawCosineSupport,
          rawCosineEvaluatorAtScale q x b * rawBucketAmplitude E b) /
            q ^ (2 : ℕ)
          =
        ((∑ b ∈ rawCosineSupport,
            rawCosineEvaluatorAtScale q x b * rawBucketAmplitude E b) -
          ∑ b ∈ rawCosineSupport, rawBucketAmplitude E b) /
            q ^ (2 : ℕ) := by rw [hzero', sub_zero]
      _ = ∑ b ∈ rawCosineSupport,
          ((Real.cos (q * rawPhaseLinear x b) - 1) / q ^ (2 : ℕ)) *
            rawBucketAmplitude E b := by
        rw [← Finset.sum_sub_distrib]
        simp_rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        unfold rawCosineEvaluatorAtScale
        field_simp [hq]
  refine hsum.congr' hcongr.symm |>.congr' ?_
  filter_upwards with _
  rfl

/-- Normalizing the direction divides its phase quadratic by its squared
norm. -/
theorem rawPhaseQuadratic_normalized (x : Fin 3 → ℝ)
    (hx : 0 < realModeNormSq x) (b : Bucket) :
    rawPhaseQuadratic
        (fun i => x i / Real.sqrt (realModeNormSq x)) b =
      rawPhaseQuadratic x b / realModeNormSq x := by
  have hsqrt : Real.sqrt (realModeNormSq x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hx)
  have hsqrt_sq :
      Real.sqrt (realModeNormSq x) ^ (2 : ℕ) = realModeNormSq x :=
    Real.sq_sqrt hx.le
  unfold rawPhaseQuadratic rawPhaseLinear
  simp only [Fin.sum_univ_three]
  field_simp [hsqrt, hx.ne']
  nlinarith

/-- `reggeTTMoment` is homogeneous under direction normalization with the
expected inverse squared-norm factor. -/
theorem reggeTTMoment_normalized (x : Fin 3 → ℝ)
    (hx : 0 < realModeNormSq x) (E : Fin 3 → Fin 3 → ℝ) :
    reggeTTMoment rawCosineSupport
        (rawPhaseQuadratic
          (fun i => x i / Real.sqrt (realModeNormSq x)))
        (rawBucketAmplitude E) =
      reggeTTMoment rawCosineSupport (rawPhaseQuadratic x)
        (rawBucketAmplitude E) / realModeNormSq x := by
  unfold reggeTTMoment reggeTTBlochFold
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  show
    -rawPhaseQuadratic (fun i => x i / Real.sqrt (realModeNormSq x)) b / 2 *
        rawBucketAmplitude E b =
      -rawPhaseQuadratic x b / 2 * rawBucketAmplitude E b / realModeNormSq x
  rw [rawPhaseQuadratic_normalized x hx b]
  field_simp [hx.ne']

/-- A nonzero integer mode has positive real squared norm. -/
theorem realModeNormSq_intCast_pos (m : Fin 3 → ℤ)
    (hm : ∃ i : Fin 3, m i ≠ 0) :
    0 < realModeNormSq (fun i => (m i : ℝ)) := by
  obtain ⟨i, hi⟩ := hm
  unfold realModeNormSq
  have hi' : (m i : ℝ) ≠ 0 := by exact_mod_cast hi
  exact Finset.sum_pos' (fun j _ => sq_nonneg (m j : ℝ))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi'⟩

/-- The commensurate evaluator is exactly the free-scale evaluator at
`q_N = 2*pi/N`. -/
theorem rawCosineEvaluator_eq_scale (N : ℕ) [NeZero N]
    (m : Fin 3 → ℤ) (b : Bucket) :
    rawCosineEvaluator N m b =
      rawCosineEvaluatorAtScale (sideScale N) (fun i => (m i : ℝ)) b := by
  unfold rawCosineEvaluator rawCosineEvaluatorAtScale rawPhaseLinear
    commensurateMomentum sideScale
  congr 1
  simp only [Fin.sum_univ_three]
  ring

/-- Exact factorization of the momentum normalization into scale squared
times the integer-mode norm squared. -/
theorem momentumNormSq_eq_scale_sq (N : ℕ) [NeZero N]
    (m : Fin 3 → ℤ) :
    momentumNormSq N m =
      sideScale N ^ (2 : ℕ) * realModeNormSq (fun i => (m i : ℝ)) := by
  unfold momentumNormSq commensurateMomentum sideScale realModeNormSq
  simp only [Fin.sum_univ_three]
  ring

/-- FINAL P1.1a HEADLINE: for every fixed nonzero integer mode, the actual
finite reduced Regge symbol, divided by `momentumNormSq`, converges to exactly
the raw Regge TT moment at the normalized real mode direction.  The literal
phase remains `(sum_i x_i * (u_i / 2))^2`. -/
theorem canonicalFiniteH_div_momentumNormSq_tendsto (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (hm : ∃ i : Fin 3, m i ≠ 0) :
    Filter.Tendsto
      (fun j : ℕ =>
        @canonicalFiniteH (j + 3) (instNeZeroAddThree j) E m /
          momentumNormSq (j + 3) m)
      Filter.atTop
      (nhds
        (reggeTTMoment rawCosineSupport
          (rawPhaseQuadratic (normalizedRealMode m))
          (rawBucketAmplitude E))) := by
  let x : Fin 3 → ℝ := fun i => (m i : ℝ)
  let s : ℝ := realModeNormSq x
  have hs : 0 < s := realModeNormSq_intCast_pos m hm
  have hq0 :
      Filter.Tendsto (fun j : ℕ => sideScale (j + 3))
        Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi)).comp
        (Filter.tendsto_add_atTop_nat 3)
    exact h.congr fun j => rfl
  have hqmem :
      ∀ᶠ j : ℕ in Filter.atTop,
        sideScale (j + 3) ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards with j
    have hden : ((j + 3 : ℕ) : ℝ) ≠ 0 := by positivity
    have hnum : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero hnum hden
  have hq :
      Filter.Tendsto (fun j : ℕ => sideScale (j + 3))
        Filter.atTop (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hq0 hqmem
  have hscale :=
    (rawCosineFold_scale_tendsto x E).comp hq
  have hdiv := hscale.div_const s
  have hlimit :
      Filter.Tendsto
        (fun j : ℕ =>
          rawCosineFoldAtScale (sideScale (j + 3)) x E /
              sideScale (j + 3) ^ (2 : ℕ) / s)
        Filter.atTop
        (nhds
          (reggeTTMoment rawCosineSupport
            (rawPhaseQuadratic (normalizedRealMode m))
            (rawBucketAmplitude E))) := by
    rw [show normalizedRealMode m =
        fun i => x i / Real.sqrt (realModeNormSq x) by
      funext i
      rfl]
    rw [reggeTTMoment_normalized x hs E]
    simpa [s] using hdiv
  have hshift : Filter.Tendsto (fun j : ℕ => j + 3)
      Filter.atTop Filter.atTop := Filter.tendsto_add_atTop_nat 3
  have hassembly :=
    hshift.eventually
      (eventually_canonicalFiniteH_eq_rawCosineBlochFold E m hm)
  refine hlimit.congr' ?_
  filter_upwards [hassembly] with j hj
  specialize hj (instNeZeroAddThree j)
  rw [hj, momentumNormSq_eq_scale_sq]
  unfold rawCosineFoldAtScale reggeTTBlochFold
  rw [div_div]
  have hsum_eq :
      (∑ b ∈ rawCosineSupport,
          rawCosineEvaluatorAtScale (sideScale (j + 3)) x b *
            rawBucketAmplitude E b) =
        ∑ b ∈ rawCosineSupport,
          rawCosineEvaluator (j + 3) m b * rawBucketAmplitude E b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [rawCosineEvaluator_eq_scale]
  rw [hsum_eq]

end

end ReggeTTContinuumLimit
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumLimit.rawCosineFoldAtScale_zero
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumLimit.rawCosineFold_scale_tendsto
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTContinuumLimit.canonicalFiniteH_div_momentumNormSq_tendsto
