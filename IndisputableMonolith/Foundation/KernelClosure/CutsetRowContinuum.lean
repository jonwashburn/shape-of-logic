import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow2Cost
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostContinuumCorollary
import IndisputableMonolith.Foundation.KernelIndependenceCore

/-!
# Cutset row: the continuum

The one purchase left in the kernel ledger after rows 1 to 6 is the step from
the rationals to the reals. The native ledger pins the cost at every positive
rational with no continuity anywhere (`structural_cost_eq_jcost_on_rationals`);
the inverted bridge carries it to the line with one word, `ContinuousOn`, and
prices that word with `irrationalShiftCost`. Row 2b's regularity half, row 1's
composition to the polynomial form, and row 3's number-theory import are each
that same step wearing a different coat.

## The blade

The floor never posts an irrational. A ratio that is not a count ratio reaches
the ledger only as the sequence of its readings floor by floor, and the octave
tower reads finer at every floor: at floor `n` the reading of `x` is the least
count ratio with denominator `2^n` that is not below `x`. The floor word is
therefore

  the cost of a ratio the floor does not post is what its floors read,

`FloorReadable F`: for every positive `x`, `F (reading n x) → F x`. This is a
definition (provenance `definition`), of the same kind as the clock row's
"finest recognizer of change" and the D=3 row's "a posting is a record". It
mentions neither continuity nor `J`.

## The cut

* Floor: `RationalNative F`, the cost agrees with the native answer at every
  positive rational. Every inhabitant of the native structural ledger has it
  (`rationalNative_of_native`), with no continuity used.
* Sentence: `ContinuousOn F (Ioi 0)`, the word the bridge charges for.
* Real: `Jcost`, floor-readable because continuous.
* Violator: `wildCost`, a solution of the composition law on the whole line
  (`wildCost_compositionLaw`), equal to `J` at every positive rational
  (`wildCost_rationalNative`), different from `J` at some positive real
  (`wildCost_ne_jcost`), hence neither continuous nor floor-readable. It is the
  classical wild solution: `cosh (a (log x)) - 1` with `a` additive but not
  linear, built from a nonzero ℚ-linear functional that vanishes on the ℚ-span
  of the logs of the rationals. That span is countable and the line is not, so
  the functional exists (`logSpan_ne_top`, `Submodule.exists_le_ker_of_lt_top`).
  The point of this violator over `irrationalShiftCost` is that imposing the
  composition law on the reals does not exclude it; only the blade does.
* Exclusion: a rational-native, floor-readable cost is `J` on `(0, ∞)`
  (`eq_jcost_of_floorReadable`), hence continuous.

## What closes under the blade

`eq_jcost_of_floorReadable` gives `F = J` on the positives, so under the blade
`F` satisfies the composition law on the reals (`compositionLaw_of_floorReadable`),
is monotone in imbalance (`monotone_of_floorReadable`, row 2b's regularity half),
and is calibrated (`calibrated_of_floorReadable`, row 3's real exponent, with no
external theorem). None of these is assumed anywhere in this module.

## Shape

The blade is not private to `J`: every function continuous on `(0, ∞)` passes
it (`floorReadable_of_continuousOn`). Under the floor the blade and the sentence
coincide (`floorReadable_iff_continuousOn_of_rationalNative`), so this row is a
merge in the sense of the earlier rows: the priced word "continuous" is the floor
word "what its floors read" in other words. The countermodel is what makes it a
cut and not bookkeeping: the wild cost is on the floor and off the blade.

Grade: MODEL. Continuity is a theorem under a definition of what a non-count
ratio is to the ledger; it is not derived from distinction.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace RowContinuum

open Cost Cost.FunctionalEquation Filter Topology
open PrimitiveRecognitionCalculus PrimitiveRecognitionCalculus.PRCJCost
open Row2Cost

noncomputable section

/-! ## The floor: the native ledger on count ratios -/

/-- The cost agrees with the native answer at every positive rational. -/
def RationalNative (F : ℝ → ℝ) : Prop :=
  ∀ t : ℚ, 0 < t → F (t : ℝ) = Jcost (t : ℝ)

/-- Every inhabitant of the native structural ledger is rational-native, with no
continuity used (`structural_cost_eq_jcost_on_rationals`). -/
theorem rationalNative_of_native {F : ℝ → ℝ} {G : RatioOrbit → RatioOrbit}
    (hG : PRCStructuralNativeCostHypotheses G)
    (hrestrict : ∀ q : RatioOrbit, 0 < q.toRat →
      F ((q.toRat : ℚ) : ℝ) = (((G q).toRat : ℚ) : ℝ)) :
    RationalNative F := by
  intro t ht
  have hq : (0 : ℚ) < (ratioOrbitOfRat t).toRat := by
    rw [ratioOrbitOfRat_toRat]; exact ht
  have h₁ := hrestrict (ratioOrbitOfRat t) hq
  rw [ratioOrbitOfRat_toRat] at h₁
  rw [h₁]
  exact structural_cost_eq_jcost_on_rationals hG t

theorem jcost_rationalNative : RationalNative Jcost := fun _ _ => rfl

/-! ## Readings: what floor `n` posts for a ratio `x` -/

/-- The floor-`n` reading of `x`: the least count ratio with denominator `2^n`
not below `x`. -/
def readingQ (n : ℕ) (x : ℝ) : ℚ := (⌈x * 2 ^ n⌉₊ : ℚ) / 2 ^ n

/-- The same reading, seen on the line. -/
def reading (n : ℕ) (x : ℝ) : ℝ := (readingQ n x : ℝ)

theorem reading_eq (n : ℕ) (x : ℝ) : reading n x = (⌈x * 2 ^ n⌉₊ : ℝ) / 2 ^ n := by
  unfold reading readingQ
  push_cast
  ring

theorem readingQ_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < readingQ n x := by
  unfold readingQ
  have h : 0 < ⌈x * 2 ^ n⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have h' : (0 : ℚ) < (⌈x * 2 ^ n⌉₊ : ℚ) := by exact_mod_cast h
  positivity

theorem le_reading (x : ℝ) (n : ℕ) : x ≤ reading n x := by
  rw [reading_eq]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [le_div_iff₀ h2]
  exact Nat.le_ceil _

theorem reading_lt {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : reading n x < x + 1 / 2 ^ n := by
  rw [reading_eq]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2]
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ x * 2 ^ n by positivity)
  calc (⌈x * 2 ^ n⌉₊ : ℝ) < x * 2 ^ n + 1 := hc
    _ = (x + 1 / 2 ^ n) * 2 ^ n := by field_simp

/-- The readings converge to the ratio they read. -/
theorem tendsto_reading {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => reading n x) atTop (𝓝 x) := by
  have hlow : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  have hpow : Tendsto (fun n : ℕ => (1 / (2 : ℝ)) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hup : Tendsto (fun n : ℕ => x + 1 / (2 : ℝ) ^ n) atTop (𝓝 (x + 0)) := by
    refine hlow.add ?_
    refine hpow.congr (fun n => ?_)
    exact one_div_pow 2 n
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup
    (fun n => le_reading x n) (fun n => (reading_lt hx.le n).le)

/-! ## The blade -/

/-- **Floor readability.** The cost of a ratio the floor does not post is what
its floors read: `F (reading n x) → F x`. A definition; it names neither
continuity nor `J`. -/
def FloorReadable (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → Tendsto (fun n : ℕ => F (reading n x)) atTop (𝓝 (F x))

/-- The blade is not private to `J`: every cost continuous on the positives
passes it. -/
theorem floorReadable_of_continuousOn {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Ioi 0)) : FloorReadable F := by
  intro x hx
  have hc : ContinuousAt F x := hF.continuousAt (Ioi_mem_nhds hx)
  exact hc.tendsto.comp (tendsto_reading hx)

theorem jcost_floorReadable : FloorReadable Jcost :=
  floorReadable_of_continuousOn jcost_continuousOn

/-! ## The cut -/

/-- A rational-native, floor-readable cost is `J` on the positives. The native
ledger selects the answer on counts; the blade carries it to the line. -/
theorem eq_jcost_of_floorReadable {F : ℝ → ℝ} (hrat : RationalNative F)
    (hread : FloorReadable F) : ∀ x : ℝ, 0 < x → F x = Jcost x := by
  intro x hx
  have h1 : Tendsto (fun n : ℕ => F (reading n x)) atTop (𝓝 (F x)) := hread x hx
  have hJ : Tendsto (fun n : ℕ => Jcost (reading n x)) atTop (𝓝 (Jcost x)) :=
    (jcost_continuousOn.continuousAt (Ioi_mem_nhds hx)).tendsto.comp (tendsto_reading hx)
  have h2 : Tendsto (fun n : ℕ => F (reading n x)) atTop (𝓝 (Jcost x)) :=
    hJ.congr (fun n => (hrat (readingQ n x) (readingQ_pos hx n)).symm)
  exact tendsto_nhds_unique h1 h2

theorem continuousOn_of_floorReadable {F : ℝ → ℝ} (hrat : RationalNative F)
    (hread : FloorReadable F) : ContinuousOn F (Set.Ioi 0) :=
  jcost_continuousOn.congr (fun x hx => eq_jcost_of_floorReadable hrat hread x hx)

/-- Under the floor, the blade and the priced word coincide. -/
theorem floorReadable_iff_continuousOn_of_rationalNative {F : ℝ → ℝ}
    (hrat : RationalNative F) : FloorReadable F ↔ ContinuousOn F (Set.Ioi 0) :=
  ⟨continuousOn_of_floorReadable hrat, floorReadable_of_continuousOn⟩

/-! ## What closes under the blade -/

theorem jcost_eq_cosh_log {x : ℝ} (hx : 0 < x) :
    Jcost x = Real.cosh (Real.log x) - 1 := by
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_log hx]
  simp only [Jcost]

/-- `J` satisfies the composition law, by the cosh addition formulas. -/
theorem jcost_compositionLaw : SatisfiesCompositionLaw Jcost := by
  intro x y hx hy
  rw [jcost_eq_cosh_log (mul_pos hx hy), jcost_eq_cosh_log (div_pos hx hy),
    jcost_eq_cosh_log hx, jcost_eq_cosh_log hy,
    Real.log_mul hx.ne' hy.ne', Real.log_div hx.ne' hy.ne', Real.cosh_add, Real.cosh_sub]
  ring

/-- Row 1's residual: under the blade the cost composes by the law on the reals. -/
theorem compositionLaw_of_floorReadable {F : ℝ → ℝ} (hrat : RationalNative F)
    (hread : FloorReadable F) : SatisfiesCompositionLaw F := by
  intro x y hx hy
  rw [eq_jcost_of_floorReadable hrat hread _ (mul_pos hx hy),
    eq_jcost_of_floorReadable hrat hread _ (div_pos hx hy),
    eq_jcost_of_floorReadable hrat hread x hx, eq_jcost_of_floorReadable hrat hread y hy]
  exact jcost_compositionLaw x y hx hy

/-- Row 2b's regularity half: under the blade a larger imbalance never costs less. -/
theorem monotone_of_floorReadable {F : ℝ → ℝ} (hrat : RationalNative F)
    (hread : FloorReadable F) : MonotoneImbalance F := by
  have hH : ∀ t, H F t = H Jcost t := by
    intro t
    simp only [H, G]
    rw [eq_jcost_of_floorReadable hrat hread _ (Real.exp_pos t)]
  intro s hs t ht hst
  rw [hH s, hH t]
  exact jcost_monotone hs ht hst

/-- Row 3's real exponent: under the blade the cost is calibrated, with no
external theorem. -/
theorem calibrated_of_floorReadable {F : ℝ → ℝ} (hrat : RationalNative F)
    (hread : FloorReadable F) : IsCalibrated F := by
  have hG : G F = G Jcost := by
    funext t
    simp only [G]
    exact eq_jcost_of_floorReadable hrat hread _ (Real.exp_pos t)
  unfold IsCalibrated
  rw [hG]
  exact KernelIndependence.jcost_calibrated

/-! ## The violator: the classical wild solution -/

/-- The ℚ-span of the logs of the rationals. -/
def logSpan : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range (fun t : ℚ => Real.log (t : ℝ)))

theorem log_rat_mem (t : ℚ) : Real.log (t : ℝ) ∈ logSpan :=
  Submodule.subset_span ⟨t, rfl⟩

/-- Countably many logs of rationals span a countable set; the line is not. -/
theorem logSpan_countable : Countable logSpan := by
  unfold logSpan
  infer_instance

theorem logSpan_ne_top : logSpan ≠ ⊤ := by
  intro h
  have hc : Countable logSpan := logSpan_countable
  rw [h] at hc
  haveI : Countable ℝ := Countable.of_equiv _ (Submodule.topEquiv (R := ℚ) (M := ℝ)).toEquiv
  exact Cardinal.not_countable_real Set.countable_univ

theorem logSpan_lt_top : logSpan < ⊤ := lt_top_iff_ne_top.mpr logSpan_ne_top

theorem exists_shift : ∃ f : ℝ →ₗ[ℚ] ℚ, f ≠ 0 ∧ logSpan ≤ LinearMap.ker f :=
  Submodule.exists_le_ker_of_lt_top logSpan logSpan_lt_top

/-- A nonzero ℚ-linear functional vanishing on every log of a rational. -/
def shift : ℝ →ₗ[ℚ] ℚ := Classical.choose exists_shift

theorem shift_ne_zero : shift ≠ 0 := (Classical.choose_spec exists_shift).1

theorem shift_log_rat (t : ℚ) : shift (Real.log (t : ℝ)) = 0 :=
  LinearMap.mem_ker.mp ((Classical.choose_spec exists_shift).2 (log_rat_mem t))

/-- The additive, non-linear twist of the line: the identity on every log of a
rational, and not the identity. -/
def twist (u : ℝ) : ℝ := u + (shift u : ℝ)

theorem twist_add (u v : ℝ) : twist (u + v) = twist u + twist v := by
  unfold twist; rw [map_add]; push_cast; ring

theorem twist_sub (u v : ℝ) : twist (u - v) = twist u - twist v := by
  unfold twist; rw [map_sub]; push_cast; ring

theorem twist_log_rat (t : ℚ) : twist (Real.log (t : ℝ)) = Real.log (t : ℝ) := by
  unfold twist; rw [shift_log_rat]; simp

/-- The wild cost: a composition-law solution on the whole line that is `J` at
every rational and not `J`. -/
def wildCost (x : ℝ) : ℝ := Real.cosh (twist (Real.log x)) - 1

theorem wildCost_compositionLaw : SatisfiesCompositionLaw wildCost := by
  intro x y hx hy
  unfold wildCost
  rw [Real.log_mul hx.ne' hy.ne', Real.log_div hx.ne' hy.ne', twist_add, twist_sub,
    Real.cosh_add, Real.cosh_sub]
  ring

theorem wildCost_rationalNative : RationalNative wildCost := by
  intro t ht
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  unfold wildCost
  rw [twist_log_rat, jcost_eq_cosh_log ht']

/-- Somewhere the shift is nonzero and is not the reflection `-2u` (which would
let `cosh` hide it). -/
theorem exists_bad : ∃ u : ℝ, (shift u : ℝ) ≠ 0 ∧ (shift u : ℝ) ≠ -2 * u := by
  obtain ⟨u, hu⟩ : ∃ u, shift u ≠ 0 := by
    by_contra h
    push_neg at h
    exact shift_ne_zero (LinearMap.ext (fun x => by rw [h x]; rfl))
  have hu' : (shift u : ℝ) ≠ 0 := by exact_mod_cast hu
  by_cases hcase : (shift u : ℝ) = -2 * u
  · have hlog : Real.log ((2 : ℚ) : ℝ) ≠ 0 := by
      have h2 : (1 : ℝ) < ((2 : ℚ) : ℝ) := by norm_num
      exact (Real.log_pos h2).ne'
    refine ⟨u + Real.log ((2 : ℚ) : ℝ), ?_, ?_⟩
    · rw [map_add, shift_log_rat 2, add_zero]; exact hu'
    · rw [map_add, shift_log_rat 2, add_zero, hcase]
      intro h
      apply hlog
      linarith
  · exact ⟨u, hu', hcase⟩

theorem wildCost_ne_jcost : ∃ x : ℝ, 0 < x ∧ wildCost x ≠ Jcost x := by
  obtain ⟨u, hu0, hu2⟩ := exists_bad
  refine ⟨Real.exp u, Real.exp_pos u, ?_⟩
  rw [jcost_eq_cosh_log (Real.exp_pos u)]
  unfold wildCost
  rw [Real.log_exp]
  intro h
  have h' : Real.cosh (twist u) = Real.cosh u := by linarith
  have habs : |twist u| = |u| := by
    have hinj := Real.cosh_strictMonoOn.injOn
    apply hinj (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _))
    rw [Real.cosh_abs, Real.cosh_abs]
    exact h'
  unfold twist at habs
  rcases abs_eq_abs.mp habs with h1 | h1
  · exact hu0 (by linarith)
  · exact hu2 (by linarith)

/-- A rational-native cost that leaves `J` anywhere is not floor-readable. -/
theorem not_floorReadable_of_ne {F : ℝ → ℝ} (hrat : RationalNative F) {x : ℝ}
    (hx : 0 < x) (hne : F x ≠ Jcost x) : ¬ FloorReadable F :=
  fun hread => hne (eq_jcost_of_floorReadable hrat hread x hx)

/-- A rational-native cost that leaves `J` anywhere is not continuous. -/
theorem not_continuousOn_of_ne {F : ℝ → ℝ} (hrat : RationalNative F) {x : ℝ}
    (hx : 0 < x) (hne : F x ≠ Jcost x) : ¬ ContinuousOn F (Set.Ioi 0) :=
  fun hcont => hne (completion_step hcont hrat x hx)

theorem wildCost_not_floorReadable : ¬ FloorReadable wildCost := by
  obtain ⟨x, hx, hne⟩ := wildCost_ne_jcost
  exact not_floorReadable_of_ne wildCost_rationalNative hx hne

theorem wildCost_not_continuousOn : ¬ ContinuousOn wildCost (Set.Ioi 0) := by
  obtain ⟨x, hx, hne⟩ := wildCost_ne_jcost
  exact not_continuousOn_of_ne wildCost_rationalNative hx hne

/-! ## The blade is not continuity in disguise

Off the floor, floor readability is strictly weaker than continuity: the step
cost `if 1 ≤ x then 1 else 0` reads correctly at every floor (its readings never
fall below the ratio) and is not continuous. The floor is what makes the two
coincide. -/

/-- A right-continuous step: floor-readable, not continuous. -/
def stepCost (x : ℝ) : ℝ := if 1 ≤ x then 1 else 0

theorem stepCost_floorReadable : FloorReadable stepCost := by
  intro x hx
  rcases lt_or_ge x 1 with hlt | hge
  · have hIio : ∀ᶠ n : ℕ in atTop, reading n x ∈ Set.Iio 1 :=
      (tendsto_reading hx) (Iio_mem_nhds hlt)
    have hev : ∀ᶠ n : ℕ in atTop, stepCost x = stepCost (reading n x) := by
      filter_upwards [hIio] with n hn
      simp only [stepCost, Set.mem_Iio] at hn ⊢
      rw [if_neg (not_le.mpr hn), if_neg (not_le.mpr hlt)]
    exact tendsto_const_nhds.congr' hev
  · refine tendsto_const_nhds.congr (fun n => ?_)
    have h1 : 1 ≤ reading n x := le_trans hge (le_reading x n)
    simp only [stepCost, if_pos h1, if_pos hge]

theorem stepCost_not_continuousOn : ¬ ContinuousOn stepCost (Set.Ioi 0) := by
  intro h
  have hc : ContinuousAt stepCost 1 := h.continuousAt (Ioi_mem_nhds one_pos)
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℝ)) |>.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [sub_zero] at this
  have h1 : Tendsto (fun n : ℕ => stepCost (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 (stepCost 1)) :=
    hc.tendsto.comp hseq
  have h0 : Tendsto (fun n : ℕ => stepCost (1 - 1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr (fun n => ?_)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : (1 : ℝ) - 1 / ((n : ℝ) + 1) < 1 := by linarith
    simp only [stepCost, if_neg (not_le.mpr hlt)]
  have h01 := tendsto_nhds_unique h0 h1
  simp [stepCost] at h01

/-- The bridge's own purchase witness also fails the blade. -/
theorem irrationalShiftCost_not_floorReadable : ¬ FloorReadable irrationalShiftCost :=
  not_floorReadable_of_ne (fun t _ => irrationalShiftCost_of_rat t)
    (Real.sqrt_pos.mpr (by norm_num)) irrationalShiftCost_ne_at_sqrt_two

/-! ## The row -/

/-- The continuum row: floor = rational-native, sentence = continuous on the
positives, blade = floor-readable, real = `J`, violator = the wild cost. -/
def row : CutsetRow (ℝ → ℝ) where
  Floor := RationalNative
  Sentence := fun F => ContinuousOn F (Set.Ioi 0)
  Blade := FloorReadable
  provenance := .definition "the cost of a ratio the floor does not post is what its floors read"
  real := Jcost
  real_floor := jcost_rationalNative
  blade_real := jcost_floorReadable
  violator := wildCost
  violator_floor := wildCost_rationalNative
  violator_violates := wildCost_not_continuousOn
  blade_kills_violator := wildCost_not_floorReadable
  exclusion := fun _ hf hs hb => hs (continuousOn_of_floorReadable hf hb)

/-! ## Certificate -/

structure Cert : Prop where
  /-- Floor plus blade forces the sentence. -/
  forces : ∀ F, row.Floor F → row.Blade F → row.Sentence F
  /-- The violating class is non-empty. -/
  class_nonempty : ∃ F, row.Floor F ∧ ¬ row.Sentence F
  /-- The blade varies. -/
  blade_varies : ∃ F G, row.Blade F ∧ ¬ row.Blade G
  /-- The violator satisfies the composition law on the whole line: the law
  does not exclude it, the blade does. -/
  violator_lawful : SatisfiesCompositionLaw wildCost
  /-- Under the blade the cost is `J` on the positives. -/
  answer : ∀ F, RationalNative F → FloorReadable F → ∀ x, 0 < x → F x = Jcost x
  /-- The three residuals close under the blade. -/
  residuals : ∀ F, RationalNative F → FloorReadable F →
    SatisfiesCompositionLaw F ∧ MonotoneImbalance F ∧ IsCalibrated F
  /-- The blade is not private to `J`. -/
  blade_not_private : ∀ F, ContinuousOn F (Set.Ioi 0) → FloorReadable F
  /-- Off the floor the blade is strictly weaker than the sentence: it is not
  continuity renamed. -/
  blade_strictly_weaker : ∃ F, FloorReadable F ∧ ¬ ContinuousOn F (Set.Ioi 0)
  /-- The native ledger lands on the floor with no continuity. -/
  native_on_floor : ∀ (F : ℝ → ℝ) (G : RatioOrbit → RatioOrbit),
    PRCStructuralNativeCostHypotheses G →
    (∀ q : RatioOrbit, 0 < q.toRat → F ((q.toRat : ℚ) : ℝ) = (((G q).toRat : ℚ) : ℝ)) →
    RationalNative F

theorem cert : Cert where
  forces := row.forces
  class_nonempty := row.class_nonempty
  blade_varies := row.blade_varies
  violator_lawful := wildCost_compositionLaw
  answer := fun _ hrat hread => eq_jcost_of_floorReadable hrat hread
  residuals := fun _ hrat hread =>
    ⟨compositionLaw_of_floorReadable hrat hread, monotone_of_floorReadable hrat hread,
      calibrated_of_floorReadable hrat hread⟩
  blade_not_private := fun _ h => floorReadable_of_continuousOn h
  blade_strictly_weaker := ⟨stepCost, stepCost_floorReadable, stepCost_not_continuousOn⟩
  native_on_floor := fun _ _ hG hr => rationalNative_of_native hG hr

end

end RowContinuum
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith
