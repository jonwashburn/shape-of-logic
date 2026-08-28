import Mathlib
import IndisputableMonolith.Patterns

/-!
# What a recognition outcome counts: the Born law of a complete pass

A recognition act cuts a state into parts, one per outcome, and a law of
recognition says how much of the pass each part carries. Three conditions, none
of them about squares:

* a count is nonnegative,
* a complete pass counts one,
* two orthogonal parts that fit inside one pass count separately exactly as they
  count together.

`PassLaw.count_eq_sq_norm` is the law: on a real inner product space carrying
three or more independent directions, those three conditions force the count of
a part to be the square of its length. `PassLaw.count_of_reading` reads that as a
probability rule for a reading with any finite number of outcomes: each outcome
carries the squared length of the component it selects, and the outcomes of one
reading carry the whole pass between them.

## Why three directions

The pass clause speaks about every unit state, not about one frame. Fix two parts
of equal length below one. With a third direction available there is a part
orthogonal to both, of exactly the length that completes either one to a unit
state; each completion counts one, so the two parts count the same. Length is
therefore all a law can read, and Cauchy's functional equation on the unit
interval, closed by monotonicity rather than by continuity, finishes the job. In
two dimensions no direction is orthogonal to two given ones, which is where
counterexamples to Gleason-type statements live. No frame-function theorem is
used, and none is available in Mathlib.

## The ledger's own reading

`blockReading` is the witness that the many-outcome hypothesis is inhabited by a
ledger object: a map sending each configuration to the outcome whose block
contains it, and the parts the reading selects are the coarse-grainings of the
pass over those blocks. Those parts are mutually orthogonal and they add to the
state, so `count_blockReading` gives the outcome probabilities of a coarse reading
of the pass: the sum of the squared amplitudes of the configurations the outcome
contains, summing to one over the outcomes. On the ledger's `Pattern d` this is a
reading of the pass by blocks of configurations
(`count_blockReading_pattern`).

`bornPassLaw` exhibits a law, so the conditions are not vacuous, and three decoys
fail one named clause each: counting the length rather than its square and
counting the fourth power both fail the orthogonal split, while twice the square
fails the pass and satisfies the other two.
-/

namespace IndisputableMonolith
namespace Foundation
namespace BornLawFromThePass

open scoped BigOperators
open IndisputableMonolith.Patterns

/-! ## Part 1: counts over a partition of one pass

The arithmetic content, stated for a bare function of the fraction of the pass a
part carries. Nothing here mentions recognition. -/

/-- A count is additive over a partition of the unit pass. -/
def CountsAdd (h : ℝ → ℝ) : Prop :=
  ∀ u v : ℝ, 0 ≤ u → 0 ≤ v → u + v ≤ 1 → h (u + v) = h u + h v

/-- A count is nonnegative on the pass. -/
def CountsNonneg (h : ℝ → ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h t

lemma counts_zero {h : ℝ → ℝ} (hadd : CountsAdd h) : h 0 = 0 := by
  have h00 := hadd 0 0 le_rfl le_rfl (by norm_num)
  simp only [add_zero] at h00
  linarith

/-- Nonnegativity plus additivity make a count monotone: a bigger part of the
pass carries at least as much. -/
lemma counts_mono {h : ℝ → ℝ} (hadd : CountsAdd h) (hnn : CountsNonneg h)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) : h s ≤ h t := by
  have hsplit := hadd s (t - s) hs (by linarith) (by linarith)
  have hEq : s + (t - s) = t := by ring
  rw [hEq] at hsplit
  have hnonneg : 0 ≤ h (t - s) := hnn _ (by linarith) (by linarith)
  linarith

/-- A count of `n` equal parts is `n` times the count of one. -/
lemma counts_nat_mul {h : ℝ → ℝ} (hadd : CountsAdd h) :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → (n : ℝ) * t ≤ 1 → h ((n : ℝ) * t) = (n : ℝ) * h t := by
  intro n
  induction n with
  | zero => intro t _ _; simp [counts_zero hadd]
  | succ n ih =>
      intro t ht hle
      have hcast : ((n + 1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by push_cast; ring
      rw [hcast] at hle ⊢
      have hn0 : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
      have hnt : (n : ℝ) * t ≤ 1 := by linarith
      rw [hadd _ _ hn0 ht hle, ih t ht hnt]
      push_cast; ring

/-- On the rationals of the pass the count is already linear. -/
lemma counts_rat {h : ℝ → ℝ} (hadd : CountsAdd h) {k m : ℕ} (hm : 0 < m) (hkm : k ≤ m) :
    h ((k : ℝ) / m) = (k : ℝ) / m * h 1 := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hone : ((m : ℝ)) * (1 / m) = 1 := by field_simp
  have hstep : h ((m : ℝ) * (1 / m)) = (m : ℝ) * h (1 / m) :=
    counts_nat_mul hadd m (1 / m) (by positivity) (by rw [hone])
  rw [hone] at hstep
  have hinv : h (1 / m) = h 1 / m := by
    field_simp at hstep ⊢
    linarith
  have hkle : (k : ℝ) * (1 / m) ≤ 1 := by
    rw [mul_one_div, div_le_one hm0]
    exact_mod_cast hkm
  have hk : h ((k : ℝ) * (1 / m)) = (k : ℝ) * h (1 / m) :=
    counts_nat_mul hadd k (1 / m) (by positivity) hkle
  rw [mul_one_div] at hk
  rw [hk, hinv]
  field_simp

/-- **Counts over a partition are linear.** A nonnegative additive count on the
unit pass is determined by what it gives the whole pass. This is Cauchy's
functional equation on an interval, closed by monotonicity rather than by
continuity, which is why no analytic hypothesis appears. -/
theorem counts_linear {h : ℝ → ℝ} (hadd : CountsAdd h) (hnn : CountsNonneg h)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : h t = t * h 1 := by
  have h1nn : 0 ≤ h 1 := hnn 1 zero_le_one le_rfl
  rcases lt_or_eq_of_le ht1 with htlt | hteq
  · have key : ∀ m : ℕ, 0 < m → |h t - t * h 1| ≤ h 1 / m := by
      intro m hm
      have hmR : (0:ℝ) < m := by exact_mod_cast hm
      have htm0 : 0 ≤ t * m := by positivity
      have hfl : ((⌊t * m⌋₊ : ℕ) : ℝ) ≤ t * m := Nat.floor_le htm0
      have hfl2 : t * m < (⌊t * m⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
      have hnm : ⌊t * m⌋₊ < m := by
        have hlt : ((⌊t * m⌋₊ : ℕ) : ℝ) < m := by
          calc ((⌊t * m⌋₊ : ℕ) : ℝ) ≤ t * m := hfl
            _ < 1 * m := by exact mul_lt_mul_of_pos_right htlt hmR
            _ = m := one_mul _
        exact_mod_cast hlt
      set n : ℕ := ⌊t * m⌋₊ with hn_def
      have hlow : (n : ℝ) / m ≤ t := by rw [div_le_iff₀ hmR]; exact hfl
      have hhigh : t ≤ ((n : ℝ) + 1) / m := by rw [le_div_iff₀ hmR]; linarith
      have hn1m : ((n : ℝ) + 1) / m ≤ 1 := by
        rw [div_le_one hmR]
        have : (n : ℕ) + 1 ≤ m := hnm
        exact_mod_cast this
      have e1 : h ((n : ℝ) / m) = (n : ℝ) / m * h 1 := counts_rat hadd hm hnm.le
      have e2 : h (((n : ℝ) + 1) / m) = ((n : ℝ) + 1) / m * h 1 := by
        have hcr := counts_rat hadd hm (Nat.succ_le_of_lt hnm)
        push_cast at hcr
        exact hcr
      have m1 : h ((n : ℝ) / m) ≤ h t :=
        counts_mono hadd hnn (by positivity) hlow ht1
      have m2 : h t ≤ h (((n : ℝ) + 1) / m) :=
        counts_mono hadd hnn (by positivity) hhigh hn1m
      rw [e1] at m1
      rw [e2] at m2
      have hgap : ((n : ℝ) + 1) / m * h 1 - (n : ℝ) / m * h 1 = h 1 / m := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_sub_div_same]
        congr 1
        ring
      have hup : t * h 1 ≤ ((n : ℝ) + 1) / m * h 1 :=
        mul_le_mul_of_nonneg_right hhigh h1nn
      have hdown : (n : ℝ) / m * h 1 ≤ t * h 1 :=
        mul_le_mul_of_nonneg_right hlow h1nn
      rw [abs_le]
      constructor <;> linarith
    rcases eq_or_ne (h t) (t * h 1) with heq | hne
    · exact heq
    · exfalso
      have hd : 0 < |h t - t * h 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨m, hm⟩ := exists_nat_gt (h 1 / |h t - t * h 1|)
      have hNpos : 0 < m + 1 := Nat.succ_pos m
      have hNR : (0:ℝ) < (m : ℝ) + 1 := by positivity
      have hlt : h 1 / |h t - t * h 1| < (m : ℝ) + 1 := by linarith
      have hbound : h 1 / ((m : ℕ) + 1 : ℝ) < |h t - t * h 1| := by
        rw [div_lt_iff₀ hNR]
        rw [div_lt_iff₀ hd] at hlt
        linarith
      have := key (m + 1) hNpos
      push_cast at this
      linarith
  · rw [hteq]; ring

/-! ## Part 2: a law of recognition on one recognizer -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **A law of recognition.** A recognition act selects a part of the state; a law
says how much of the pass that part carries. The three conditions are the
arithmetic of a pass: a count is nonnegative, a complete pass counts one, and two
orthogonal parts that fit inside one pass count separately as they count together.

Nothing here says the count is quadratic, or smooth, or a function of the part's
length rather than of the part. -/
structure PassLaw (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- The count a selected part carries. -/
  count : E → ℝ
  /-- A count is nonnegative. -/
  nonneg : ∀ c : E, 0 ≤ count c
  /-- A complete pass counts one. -/
  unit : ∀ ψ : E, ‖ψ‖ = 1 → count ψ = 1
  /-- Orthogonal parts of one pass count separately as they count together. -/
  split : ∀ v w : E, inner ℝ v w = (0:ℝ) → ‖v + w‖ ≤ 1 →
    count (v + w) = count v + count w

namespace PassLaw

variable (L : PassLaw E)

/-- Nothing counts nothing. -/
lemma count_zero : L.count (0 : E) = 0 := by
  have h := L.split (0 : E) 0 (by simp) (by simp)
  simp only [add_zero] at h
  linarith

end PassLaw

/-! ### A direction orthogonal to two, when three are available -/

/-- With three or more independent directions there is a part of any prescribed
length orthogonal to two given ones. -/
lemma exists_orthogonal_to_pair [FiniteDimensional ℝ E]
    (hrank : 3 ≤ Module.finrank ℝ E) (u u' : E) {r : ℝ} (hr : 0 ≤ r) :
    ∃ c : E, ‖c‖ = r ∧ inner ℝ u c = (0:ℝ) ∧ inner ℝ u' c = (0:ℝ) := by
  classical
  set K : Submodule ℝ E := Submodule.span ℝ ({u, u'} : Set E) with hK
  have hcardset : (({u, u'} : Set E)).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hKle : Module.finrank ℝ K ≤ 2 :=
    le_trans (finrank_span_le_card ({u, u'} : Set E)) hcardset
  have hsum : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = Module.finrank ℝ E :=
    K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  have hnt : Nontrivial Kᗮ := Module.finrank_pos_iff.mp hpos
  obtain ⟨z, hz⟩ := exists_ne (0 : Kᗮ)
  have hzmem : (z : E) ∈ Kᗮ := z.2
  have hznz : (z : E) ≠ 0 := by
    intro h
    exact hz (Subtype.ext h)
  have hznorm : 0 < ‖(z : E)‖ := norm_pos_iff.mpr hznz
  refine ⟨(r / ‖(z : E)‖) • (z : E), ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  · have hu : u ∈ K := Submodule.subset_span (by simp)
    have := hzmem u hu
    rw [real_inner_smul_right, this, mul_zero]
  · have hu' : u' ∈ K := Submodule.subset_span (by simp)
    have := hzmem u' hu'
    rw [real_inner_smul_right, this, mul_zero]

/-- Three or more directions give a unit part. -/
lemma exists_unit [FiniteDimensional ℝ E] (hrank : 3 ≤ Module.finrank ℝ E) :
    ∃ e : E, ‖e‖ = 1 := by
  obtain ⟨c, hc, -, -⟩ := exists_orthogonal_to_pair hrank (0 : E) 0 (r := 1) zero_le_one
  exact ⟨c, hc⟩

/-- Three or more directions give two orthogonal unit parts. -/
lemma exists_orthonormal_pair [FiniteDimensional ℝ E] (hrank : 3 ≤ Module.finrank ℝ E) :
    ∃ e f : E, ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ inner ℝ e f = (0:ℝ) := by
  obtain ⟨e, he⟩ := exists_unit hrank
  obtain ⟨f, hf, hef, -⟩ := exists_orthogonal_to_pair hrank e e (r := 1) zero_le_one
  exact ⟨e, f, he, hf, hef⟩

/-- Two orthogonal parts of equal length that together make a whole pass. -/
lemma exists_halves [FiniteDimensional ℝ E] (hrank : 3 ≤ Module.finrank ℝ E) :
    ∃ v w : E, inner ℝ v w = (0:ℝ) ∧ ‖v‖ ^ 2 = 1/2 ∧ ‖w‖ ^ 2 = 1/2 ∧ ‖v + w‖ = 1 := by
  obtain ⟨e, f, he, hf, hef⟩ := exists_orthonormal_pair hrank
  refine ⟨Real.sqrt (1/2) • e, Real.sqrt (1/2) • f, ?_, ?_, ?_, ?_⟩
  · rw [real_inner_smul_left, real_inner_smul_right, hef]; ring
  · rw [norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  · rw [norm_smul, hf, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
  · have ho : inner ℝ (Real.sqrt (1/2) • e) (Real.sqrt (1/2) • f) = (0:ℝ) := by
      rw [real_inner_smul_left, real_inner_smul_right, hef]; ring
    have hv : ‖(Real.sqrt (1/2) • e : E)‖ ^ 2 = 1/2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
    have hw : ‖(Real.sqrt (1/2) • f : E)‖ ^ 2 = 1/2 := by
      rw [norm_smul, hf, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by norm_num)]
    have hsq : ‖(Real.sqrt (1/2) • e : E) + Real.sqrt (1/2) • f‖ ^ 2 = 1 := by
      rw [norm_add_sq_real, ho, hv, hw]; ring
    have hnn : 0 ≤ ‖(Real.sqrt (1/2) • e : E) + Real.sqrt (1/2) • f‖ := norm_nonneg _
    nlinarith

namespace PassLaw

variable [FiniteDimensional ℝ E] (L : PassLaw E)

/-- **A law cannot read the direction.** Two parts of the same length below one
carry the same count, because a third direction completes either of them to a
whole pass, and a whole pass counts one. This is where three directions are
needed, and where two would leave the direction free. -/
lemma count_isotropic (hrank : 3 ≤ Module.finrank ℝ E) (u u' : E)
    (hnorm : ‖u‖ = ‖u'‖) (hle : ‖u‖ ≤ 1) : L.count u = L.count u' := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [L.unit u heq, L.unit u' (by rw [← hnorm]; exact heq)]
  · have hsq : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
    obtain ⟨c, hcnorm, hcu, hcu'⟩ :=
      exists_orthogonal_to_pair hrank u u' (r := Real.sqrt (1 - ‖u‖ ^ 2))
        (Real.sqrt_nonneg _)
    have hcsq : ‖c‖ ^ 2 = 1 - ‖u‖ ^ 2 := by
      rw [hcnorm, Real.sq_sqrt (by linarith)]
    have hunit : ∀ z : E, ‖z‖ = ‖u‖ → inner ℝ z c = (0:ℝ) → ‖z + c‖ = 1 := by
      intro z hz hzc
      have hadd : ‖z + c‖ ^ 2 = ‖z‖ ^ 2 + ‖c‖ ^ 2 := by
        rw [norm_add_sq_real, hzc]; ring
      have hone : ‖z + c‖ ^ 2 = 1 := by rw [hadd, hz, hcsq]; ring
      have hnn : 0 ≤ ‖z + c‖ := norm_nonneg _
      nlinarith
    have hu := L.split u c hcu (by rw [hunit u rfl hcu])
    have hu' := L.split u' c hcu' (by rw [hunit u' hnorm.symm hcu'])
    rw [L.unit _ (hunit u rfl hcu)] at hu
    rw [L.unit _ (hunit u' hnorm.symm hcu')] at hu'
    linarith

/-! ### Reading the count along one direction -/

/-- The count of a part of squared length `t`, read along one direction. -/
noncomputable def frac (L : PassLaw E) (e : E) : ℝ → ℝ :=
  fun t => L.count (Real.sqrt t • e)

lemma norm_along {e : E} (he : ‖e‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖(Real.sqrt t • e : E)‖ = Real.sqrt t := by
  rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]

lemma count_along_eq_frac (hrank : 3 ≤ Module.finrank ℝ E) {e : E} (he : ‖e‖ = 1)
    (z : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : ‖z‖ = Real.sqrt t) :
    L.count z = L.frac e t := by
  have hunfold : L.frac e t = L.count (Real.sqrt t • e) := rfl
  rw [hunfold]
  refine L.count_isotropic hrank z _ ?_ ?_
  · rw [hz, norm_along he ht]
  · rw [hz]
    calc Real.sqrt t ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ht1
      _ = 1 := Real.sqrt_one

lemma frac_nonneg (e : E) : CountsNonneg (L.frac e) := fun _ _ _ => L.nonneg _

lemma frac_one {e : E} (he : ‖e‖ = 1) : L.frac e 1 = 1 := by
  refine L.unit _ ?_
  rw [norm_along he zero_le_one, Real.sqrt_one]

/-- **The count is additive in the fraction of the pass.** Two orthogonal
directions carry the two parts of a split, and isotropy reads both counts along
one direction. -/
lemma frac_add (hrank : 3 ≤ Module.finrank ℝ E) {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hef : inner ℝ e f = (0:ℝ)) : CountsAdd (L.frac e) := by
  intro u v hu hv huv
  have n₁ : ‖(Real.sqrt u • e : E)‖ = Real.sqrt u := norm_along he hu
  have n₂ : ‖(Real.sqrt v • f : E)‖ = Real.sqrt v := norm_along hf hv
  have o12 : inner ℝ (Real.sqrt u • e : E) (Real.sqrt v • f) = (0:ℝ) := by
    rw [real_inner_smul_left, real_inner_smul_right, hef]; ring
  have n12 : ‖(Real.sqrt u • e : E) + Real.sqrt v • f‖ = Real.sqrt (u + v) := by
    have hsq : ‖(Real.sqrt u • e : E) + Real.sqrt v • f‖ ^ 2 = u + v := by
      rw [norm_add_sq_real, o12, n₁, n₂, Real.sq_sqrt hu, Real.sq_sqrt hv]; ring
    have hnn : 0 ≤ ‖(Real.sqrt u • e : E) + Real.sqrt v • f‖ := norm_nonneg _
    rw [← hsq, Real.sqrt_sq hnn]
  have hle : ‖(Real.sqrt u • e : E) + Real.sqrt v • f‖ ≤ 1 := by
    rw [n12]
    calc Real.sqrt (u + v) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt huv
      _ = 1 := Real.sqrt_one
  have hsplit := L.split (Real.sqrt u • e) (Real.sqrt v • f) o12 hle
  rw [L.count_along_eq_frac hrank he _ hu (by linarith) n₁,
      L.count_along_eq_frac hrank he _ hv (by linarith) n₂,
      L.count_along_eq_frac hrank he _ (by linarith : (0:ℝ) ≤ u + v) huv n12] at hsplit
  exact hsplit

/-- **What a recognition outcome counts is the squared length of the part it
selects.** Three conditions on a count, three or more directions to recognize
along, and no premise that the count reads the part's length rather than the
part. -/
theorem count_eq_sq_norm (hrank : 3 ≤ Module.finrank ℝ E) (c : E) (hc : ‖c‖ ≤ 1) :
    L.count c = ‖c‖ ^ 2 := by
  obtain ⟨e, f, he, hf, hef⟩ := exists_orthonormal_pair hrank
  have hnn : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hsq0 : (0:ℝ) ≤ ‖c‖ ^ 2 := sq_nonneg _
  have hsq1 : ‖c‖ ^ 2 ≤ 1 := by nlinarith
  have href : ‖c‖ = Real.sqrt (‖c‖ ^ 2) := (Real.sqrt_sq hnn).symm
  have hiso : L.count c = L.frac e (‖c‖ ^ 2) :=
    L.count_along_eq_frac hrank he c hsq0 hsq1 href
  rw [hiso, counts_linear (L.frac_add hrank he hf hef) (L.frac_nonneg e) hsq0 hsq1,
    L.frac_one he, mul_one]

/-- Any two laws agree on every part a pass can select. -/
theorem unique (L L' : PassLaw E) (hrank : 3 ≤ Module.finrank ℝ E) (c : E)
    (hc : ‖c‖ ≤ 1) : L.count c = L'.count c := by
  rw [L.count_eq_sq_norm hrank c hc, L'.count_eq_sq_norm hrank c hc]

end PassLaw

/-! ## Part 3: readings with any finite number of outcomes -/

/-- Pythagoras over a family: mutually orthogonal parts add their squared
lengths. -/
lemma sq_norm_sum {ω : Type*} {v : ω → E}
    (ho : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0:ℝ)) (s : Finset ω) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hzero : inner ℝ (v a) (∑ i ∈ s, v i) = (0:ℝ) := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        refine ho a i ?_
        intro hai
        exact ha (by rw [hai]; exact hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha, norm_add_sq_real, hzero, ih]
      ring

/-- Every part of a family that fits inside one pass fits inside one pass. -/
lemma norm_partial_le_one {ω : Type*} [Fintype ω] {v : ω → E}
    (ho : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0:ℝ))
    (hle : ‖∑ i, v i‖ ≤ 1) (s : Finset ω) : ‖∑ i ∈ s, v i‖ ≤ 1 := by
  classical
  have h1 : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := sq_norm_sum ho s
  have h2 : ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := sq_norm_sum ho Finset.univ
  have hsub : ∑ i ∈ s, ‖v i‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun _ _ _ => sq_nonneg _)
  have htot : ‖∑ i, v i‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (∑ i, v i)]
  have hs : ‖∑ i ∈ s, v i‖ ^ 2 ≤ 1 := by rw [h1]; rw [h2] at htot; linarith
  nlinarith [norm_nonneg (∑ i ∈ s, v i)]

namespace PassLaw

variable [FiniteDimensional ℝ E] (L : PassLaw E)

/-- **A count is additive over a whole family of orthogonal parts**, not only over
a pair, by the split clause applied one outcome at a time. -/
lemma count_sum {ω : Type*} [Fintype ω] {v : ω → E}
    (ho : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0:ℝ)) (hle : ‖∑ i, v i‖ ≤ 1) :
    ∀ s : Finset ω, L.count (∑ i ∈ s, v i) = ∑ i ∈ s, L.count (v i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => simpa using L.count_zero
  | @insert a s ha ih =>
      have hzero : inner ℝ (v a) (∑ i ∈ s, v i) = (0:ℝ) := by
        rw [inner_sum]
        refine Finset.sum_eq_zero ?_
        intro i hi
        refine ho a i ?_
        intro hai
        exact ha (by rw [hai]; exact hi)
      have hbound : ‖v a + ∑ i ∈ s, v i‖ ≤ 1 := by
        have := norm_partial_le_one ho hle (insert a s)
        rwa [Finset.sum_insert ha] at this
      rw [Finset.sum_insert ha, Finset.sum_insert ha, L.split _ _ hzero hbound, ih]

/-- **The Born law for a reading with any finite number of outcomes.** The parts a
reading selects are mutually orthogonal and together they are the state. Then
every outcome carries the squared length of its own part, and the outcomes of one
reading carry the whole pass between them. Nothing here restricts the number of
outcomes to two. -/
theorem count_of_reading {ω : Type*} [Fintype ω] (hrank : 3 ≤ Module.finrank ℝ E)
    {v : ω → E} (ho : ∀ i j, i ≠ j → inner ℝ (v i) (v j) = (0:ℝ))
    (hunit : ‖∑ i, v i‖ = 1) :
    (∀ i, L.count (v i) = ‖v i‖ ^ 2) ∧ ∑ i, L.count (v i) = 1 := by
  classical
  have hle : ‖∑ i, v i‖ ≤ 1 := by rw [hunit]
  refine ⟨fun i => ?_, ?_⟩
  · have hone : ‖v i‖ ≤ 1 := by
      have := norm_partial_le_one ho hle ({i} : Finset ω)
      rwa [Finset.sum_singleton] at this
    exact L.count_eq_sq_norm hrank (v i) hone
  · have hsum := L.count_sum ho hle Finset.univ
    rw [← hsum, L.unit _ hunit]

end PassLaw

/-! ## Part 4: the ledger's own reading, by blocks of configurations -/

section Blocks

variable {ι ω : Type*} [Fintype ι] [Fintype ω] [DecidableEq ω]

/-- The part of a state that one outcome's block of configurations carries. -/
noncomputable def blockPart (blk : ι → ω) (i : ω) (ψ : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun p : ι => if blk p = i then ψ p else 0)

@[simp] lemma blockPart_apply (blk : ι → ω) (i : ω) (ψ : EuclideanSpace ℝ ι) (p : ι) :
    (blockPart blk i ψ) p = if blk p = i then ψ p else 0 := by
  simp [blockPart]

/-- Different outcomes select orthogonal parts: no configuration is in two
blocks. -/
lemma blockPart_orthogonal (blk : ι → ω) (ψ : EuclideanSpace ℝ ι) {i j : ω}
    (hij : i ≠ j) :
    inner ℝ (blockPart blk i ψ) (blockPart blk j ψ) = (0:ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockPart_apply]
  refine Finset.sum_eq_zero ?_
  intro p _
  by_cases hp : blk p = i
  · simp [hp, hij]
  · simp [hp]

/-- The outcomes of a reading exhaust the state: every configuration is in exactly
one block. -/
lemma sum_blockPart (blk : ι → ω) (ψ : EuclideanSpace ℝ ι) :
    ∑ i, blockPart blk i ψ = ψ := by
  classical
  ext p
  simp only [WithLp.ofLp_sum, Finset.sum_apply, blockPart_apply]
  simp

/-- The squared length of an outcome's part is the sum of the squared amplitudes
of the configurations in its block. -/
lemma sq_norm_blockPart (blk : ι → ω) (ψ : EuclideanSpace ℝ ι) (i : ω) :
    ‖blockPart blk i ψ‖ ^ 2 = ∑ p ∈ Finset.univ.filter (fun p => blk p = i), (ψ p) ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, blockPart_apply]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases hp : blk p = i
  · simp [hp, sq]
  · simp [hp]

end Blocks

/-! ### The law's verdict on a block reading -/

/-- **The outcome probabilities of a coarse reading of the pass.** Group the
configurations into blocks, one per outcome. Then any law of recognition gives the
outcome whose block is `i` exactly the sum of the squared amplitudes of the
configurations in that block, and the outcomes sum to one. The number of outcomes
is any finite number. -/
theorem count_blockReading {ι ω : Type*} [Fintype ι] [Fintype ω] [DecidableEq ω]
    (L : PassLaw (EuclideanSpace ℝ ι)) (hcard : 3 ≤ Fintype.card ι)
    (blk : ι → ω) (ψ : EuclideanSpace ℝ ι) (hψ : ‖ψ‖ = 1) :
    (∀ i, L.count (blockPart blk i ψ)
        = ∑ p ∈ Finset.univ.filter (fun p => blk p = i), (ψ p) ^ 2)
      ∧ ∑ i, L.count (blockPart blk i ψ) = 1 := by
  classical
  have hrank : 3 ≤ Module.finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [finrank_euclideanSpace]; exact hcard
  have hsum : ‖∑ i, blockPart blk i ψ‖ = 1 := by rw [sum_blockPart blk ψ]; exact hψ
  obtain ⟨hsq, htot⟩ :=
    L.count_of_reading hrank (v := fun i => blockPart blk i ψ)
      (fun i j hij => blockPart_orthogonal blk ψ hij) hsum
  refine ⟨fun i => ?_, htot⟩
  rw [hsq i, sq_norm_blockPart blk ψ i]

/-- **The ledger's own many-outcome reading.** The configuration space of a
recognition pass over `Pattern d` carries `2 ^ d` configurations, so from `d = 2`
up the law applies: a reading of the pass by blocks of configurations gives each
outcome the sum of the squared amplitudes of the configurations it contains. -/
theorem count_blockReading_pattern {d : ℕ} (hd : 2 ≤ d) {ω : Type*} [Fintype ω]
    [DecidableEq ω] (L : PassLaw (EuclideanSpace ℝ (Pattern d)))
    (blk : Pattern d → ω) (ψ : EuclideanSpace ℝ (Pattern d)) (hψ : ‖ψ‖ = 1) :
    (∀ i, L.count (blockPart blk i ψ)
        = ∑ p ∈ Finset.univ.filter (fun p => blk p = i), (ψ p) ^ 2)
      ∧ ∑ i, L.count (blockPart blk i ψ) = 1 := by
  classical
  have hcard : Fintype.card (Pattern d) = 2 ^ d := by
    simp [Pattern]
  have h4 : 2 ^ 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h3 : 3 ≤ Fintype.card (Pattern d) := by rw [hcard]; omega
  exact count_blockReading L h3 blk ψ hψ

/-! ## Part 5: the law is inhabited, and each decoy fails a named clause -/

/-- **The Born law is a law of recognition.** The count that squares the length
satisfies all three conditions, with the split clause being Pythagoras, so the
hypothesis of the forcing theorem is not vacuous. -/
noncomputable def bornPassLaw (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : PassLaw E where
  count c := ‖c‖ ^ 2
  nonneg _ := sq_nonneg _
  unit ψ hψ := by rw [hψ]; norm_num
  split v w hvw _ := by rw [norm_add_sq_real, hvw]; ring

@[simp] lemma bornPassLaw_count (c : E) : (bornPassLaw E).count c = ‖c‖ ^ 2 := rfl

/-- The rule that counts the length rather than its square is nonnegative and
gives a complete pass one, in the exact shapes of those two fields, and fails the
split clause on two orthogonal halves of one pass. -/
theorem length_rule_fails_split_only [FiniteDimensional ℝ E]
    (hrank : 3 ≤ Module.finrank ℝ E) :
    (∀ c : E, 0 ≤ ‖c‖) ∧ (∀ ψ : E, ‖ψ‖ = 1 → ‖ψ‖ = 1) ∧
      ¬ (∀ v w : E, inner ℝ v w = (0:ℝ) → ‖v + w‖ ≤ 1 → ‖v + w‖ = ‖v‖ + ‖w‖) := by
  refine ⟨fun c => norm_nonneg c, fun _ h => h, ?_⟩
  intro hsplit
  obtain ⟨v, w, hvw, hv, hw, hvw1⟩ := exists_halves hrank
  have h := hsplit v w hvw (by rw [hvw1])
  rw [hvw1] at h
  have hvpos : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  have hwpos : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
  have hsq : (‖v‖ + ‖w‖) ^ 2 = 1 := by rw [← h]; norm_num
  nlinarith [mul_pos hvpos hwpos]

/-- The rule that counts the fourth power of the length is nonnegative and gives a
complete pass one, and fails the split clause on the same two halves. -/
theorem fourth_power_rule_fails_split_only [FiniteDimensional ℝ E]
    (hrank : 3 ≤ Module.finrank ℝ E) :
    (∀ c : E, 0 ≤ ‖c‖ ^ 4) ∧ (∀ ψ : E, ‖ψ‖ = 1 → ‖ψ‖ ^ 4 = 1) ∧
      ¬ (∀ v w : E, inner ℝ v w = (0:ℝ) → ‖v + w‖ ≤ 1 →
          ‖v + w‖ ^ 4 = ‖v‖ ^ 4 + ‖w‖ ^ 4) := by
  refine ⟨fun c => by positivity, fun ψ hψ => by rw [hψ]; norm_num, ?_⟩
  intro hsplit
  obtain ⟨v, w, hvw, hv, hw, hvw1⟩ := exists_halves hrank
  have h := hsplit v w hvw (by rw [hvw1])
  rw [hvw1] at h
  have hv4 : ‖v‖ ^ 4 = 1/4 := by nlinarith
  have hw4 : ‖w‖ ^ 4 = 1/4 := by nlinarith
  rw [hv4, hw4] at h
  norm_num at h

/-- Twice the square is nonnegative and additive over an orthogonal split, in the
exact shapes of those two fields, and fails the pass clause: a complete pass would
count two. -/
theorem twice_square_rule_fails_pass_only [FiniteDimensional ℝ E]
    (hrank : 3 ≤ Module.finrank ℝ E) :
    (∀ c : E, 0 ≤ 2 * ‖c‖ ^ 2) ∧
      (∀ v w : E, inner ℝ v w = (0:ℝ) → ‖v + w‖ ≤ 1 →
        2 * ‖v + w‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2) ∧
      ¬ (∀ ψ : E, ‖ψ‖ = 1 → 2 * ‖ψ‖ ^ 2 = 1) := by
  refine ⟨fun c => by positivity, fun v w hvw _ => by rw [norm_add_sq_real, hvw]; ring, ?_⟩
  intro hunit
  obtain ⟨e, he⟩ := exists_unit hrank
  have h := hunit e he
  rw [he] at h
  norm_num at h

/-- No law of recognition counts the length rather than its square. -/
theorem no_length_law [FiniteDimensional ℝ E] (hrank : 3 ≤ Module.finrank ℝ E) :
    ¬ ∃ L : PassLaw E, ∀ c : E, L.count c = ‖c‖ := by
  rintro ⟨L, hL⟩
  obtain ⟨v, w, hvw, hv, hw, hvw1⟩ := exists_halves hrank
  have hforced := L.count_eq_sq_norm hrank v (by nlinarith [norm_nonneg v])
  rw [hL v, hv] at hforced
  nlinarith [norm_nonneg v]

/-- No law of recognition counts the fourth power of the length. -/
theorem no_fourth_power_law [FiniteDimensional ℝ E] (hrank : 3 ≤ Module.finrank ℝ E) :
    ¬ ∃ L : PassLaw E, ∀ c : E, L.count c = ‖c‖ ^ 4 := by
  rintro ⟨L, hL⟩
  obtain ⟨v, w, hvw, hv, hw, hvw1⟩ := exists_halves hrank
  have hforced := L.count_eq_sq_norm hrank v (by nlinarith [norm_nonneg v])
  rw [hL v] at hforced
  have hv4 : ‖v‖ ^ 4 = 1/4 := by nlinarith
  rw [hv4, hv] at hforced
  norm_num at hforced

end BornLawFromThePass
end Foundation
end IndisputableMonolith

#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.PassLaw.count_eq_sq_norm
#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.PassLaw.count_of_reading
#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.count_blockReading
#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.count_blockReading_pattern
#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.no_length_law
#print axioms IndisputableMonolith.Foundation.BornLawFromThePass.twice_square_rule_fails_pass_only
