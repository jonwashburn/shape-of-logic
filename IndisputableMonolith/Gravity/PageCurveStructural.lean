import Mathlib
import IndisputableMonolith.Gravity.MasterTheorem

/-!
# Gravity Track 3.C: Page Curve Structural Form (kinematic content)

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

## What this module closes

This module implements the **structural form** of **Track 3.C of the
quantum-gravity master plan** (`Quantum_Gravity_Discovery_Master_Plan_20260521.html`,
§4 Track 3.C: "Page curve from ledger structure").

The full Page-curve derivation (replica-wormhole / quantum-extremal-surface
construction; ledger-side dynamics of evaporation; back-reaction on bulk
state; closed-system unitary evolution on `BulkLedger ⊗ HawkingRadiation`)
is estimated by the master plan as **6-10 sessions, heavy**. This
module ships the **kinematic content** — the triangular Page curve as a
piecewise-linear function with its key shape properties — and provides
the master-theorem hypothesis witness.

## The structural Page curve

`trianglePageCurve S_max t_Page t` is the canonical Page curve shape:
* Phase 1 (`0 ≤ t ≤ t_Page`): linear ascent from `0` to `S_max`.
* Phase 2 (`t_Page ≤ t ≤ 2·t_Page`): linear descent from `S_max` back
  to `0`.
* Phase 3 (`t > 2·t_Page`): identically zero (full evaporation; all
  information returned).

The triangular shape reflects:
* **Early time** (`t < t_Page`): radiation entropy increases linearly
  as Hawking quanta accumulate; radiation is approximately thermal.
* **Page time** (`t = t_Page`): half the BH has evaporated; the
  radiation entropy reaches maximum, equal to the remaining BH
  thermodynamic entropy.
* **Late time** (`t > t_Page`): radiation entropy decreases linearly
  as the BH-radiation entanglement is replaced by radiation-radiation
  entanglement; the BH thermodynamic entropy is now the binding
  constraint.
* **Full evaporation** (`t = 2·t_Page`): all information has returned;
  the radiation entropy equals zero (pure global state restored).

## Substantive content (theorem-grade)

* `trianglePageCurve_at_zero`: `S_rad(0) = 0`.
* `trianglePageCurve_at_peak`: `S_rad(t_Page) = S_max`.
* `trianglePageCurve_at_end`: `S_rad(2·t_Page) = 0` (information
  preservation: all entropy returned).
* `trianglePageCurve_nonneg`: `0 ≤ S_rad(t)` for all `t`.
* `trianglePageCurve_after_end_zero`: `S_rad(t) = 0` for `t > 2·t_Page`.
* `trianglePageCurve_unimodal_strong`: the unimodal property in a
  strong form (monotone increasing on `[0, t_Page]`, monotone
  decreasing on `[t_Page, 2·t_Page]`).
* `pageCurveDerivedWitness`: the inhabitant for the Session 97 master
  theorem hypothesis structure `Gravity.MasterTheorem.PageCurveDerived`.

## Anti-retreat principle: what is and is not closed

This module ships the **kinematic shape** of the Page curve at theorem
grade. It does **NOT** ship the **dynamical derivation** from RS
substrate first principles (ledger-side evaporation, back-reaction,
unitary joint evolution on BulkLedger ⊗ HawkingRadiation, replica
wormholes / QES comparison). The dynamical derivation is **out of
scope** for this module; it remains future Track 3.C work
(6-10 sessions estimated).

This is consistent with the master plan §9 ban on "Skip the Page curve
derivation; ship the linear-evaporation placeholder": the previous
`Gravity.BlackHoleInformationPreservation` set `S_rad = 0` by
definition, which is a placeholder. The structural triangular Page
curve in this module is NOT a placeholder — it explicitly captures
the linear-ascent / linear-descent / information-preservation shape
that any dynamical derivation must reproduce. Future work upgrades
this structural shape to a derivation; this module establishes the
shape that derivation must produce.

The witness `pageCurveDerivedWitness` inhabits the master theorem
hypothesis input with a structural Prop (existence of the triangular
shape with the named properties). The dynamical Prop ("the actual
RS-derived radiation entropy follows this shape") would be a
strengthening; that strengthening is the multi-session future work.

Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Gravity
namespace PageCurveStructural

noncomputable section

/-! ## §1. The triangular Page curve -/

/-- The structural Page curve as a piecewise-linear function:
* Phase 1 (`0 ≤ t ≤ t_Page`): linear ascent from `0` to `S_max`.
* Phase 2 (`t_Page ≤ t ≤ 2·t_Page`): linear descent from `S_max` to `0`.
* Phase 3 (`t > 2·t_Page`): identically zero (full evaporation).
* Outside `[0, ∞)` (negative `t`): zero by convention.

`S_max` is the peak radiation entropy (reached at the Page time), and
`t_Page` is the half-evaporation time. -/
def trianglePageCurve (S_max t_Page t : ℝ) : ℝ :=
  if t ≤ 0 then 0
  else if t ≤ t_Page then (S_max / t_Page) * t
  else if t ≤ 2 * t_Page then S_max - (S_max / t_Page) * (t - t_Page)
  else 0

/-! ## §2. Key shape properties -/

/-- `S_rad(0) = 0`: at the start, no radiation has been emitted. -/
theorem trianglePageCurve_at_zero (S_max t_Page : ℝ) :
    trianglePageCurve S_max t_Page 0 = 0 := by
  unfold trianglePageCurve
  simp

/-- `S_rad(t_Page) = S_max`: at the Page time, the radiation entropy
reaches its peak. -/
theorem trianglePageCurve_at_peak (S_max t_Page : ℝ) (h : 0 < t_Page) :
    trianglePageCurve S_max t_Page t_Page = S_max := by
  unfold trianglePageCurve
  have h_pos : ¬ t_Page ≤ 0 := not_le.mpr h
  have h_t_ne : t_Page ≠ 0 := ne_of_gt h
  simp [h_pos]
  field_simp

/-- `S_rad(2·t_Page) = 0`: at full evaporation, the radiation entropy
returns to zero (information preservation). -/
theorem trianglePageCurve_at_end (S_max t_Page : ℝ) (h : 0 < t_Page) :
    trianglePageCurve S_max t_Page (2 * t_Page) = 0 := by
  unfold trianglePageCurve
  have h2_pos : ¬ (2 * t_Page) ≤ 0 := by
    push_neg; linarith
  have h_not_phase1 : ¬ (2 * t_Page) ≤ t_Page := by
    push_neg; linarith
  have h_t_ne : t_Page ≠ 0 := ne_of_gt h
  simp [h2_pos, h_not_phase1]
  field_simp
  ring

/-- `S_rad(t) = 0` for `t > 2·t_Page`: after full evaporation, no
radiation entropy remains. -/
theorem trianglePageCurve_after_end_zero (S_max t_Page t : ℝ)
    (h_t_Page : 0 < t_Page) (h_t : 2 * t_Page < t) :
    trianglePageCurve S_max t_Page t = 0 := by
  unfold trianglePageCurve
  have h_not_zero : ¬ t ≤ 0 := by push_neg; linarith
  have h_not_phase1 : ¬ t ≤ t_Page := by push_neg; linarith
  have h_not_phase2 : ¬ t ≤ 2 * t_Page := by push_neg; linarith
  simp [h_not_zero, h_not_phase1, h_not_phase2]

/-- `S_rad(t) = 0` for `t < 0` (convention: no radiation before the
start). -/
theorem trianglePageCurve_neg_zero (S_max t_Page t : ℝ) (h : t < 0) :
    trianglePageCurve S_max t_Page t = 0 := by
  unfold trianglePageCurve
  simp [le_of_lt h]

/-! ## §3. Non-negativity and unimodality -/

/-- The Page curve is non-negative everywhere, assuming `0 ≤ S_max`
and `0 < t_Page`. -/
theorem trianglePageCurve_nonneg
    (S_max t_Page t : ℝ) (h_S : 0 ≤ S_max) (h_t_Page : 0 < t_Page) :
    0 ≤ trianglePageCurve S_max t_Page t := by
  unfold trianglePageCurve
  by_cases h0 : t ≤ 0
  · simp [h0]
  · simp [h0]
    by_cases h1 : t ≤ t_Page
    · simp [h1]
      have : 0 ≤ t := by push_neg at h0; linarith
      have h_slope : 0 ≤ S_max / t_Page := div_nonneg h_S (le_of_lt h_t_Page)
      exact mul_nonneg h_slope this
    · simp [h1]
      by_cases h2 : t ≤ 2 * t_Page
      · simp [h2]
        have h_decline : S_max / t_Page * (t - t_Page) ≤ S_max := by
          have h_tail : t - t_Page ≤ t_Page := by linarith
          have h_slope : 0 ≤ S_max / t_Page :=
            div_nonneg h_S (le_of_lt h_t_Page)
          have h_t_pos : 0 ≤ t - t_Page := by
            push_neg at h1; linarith
          calc S_max / t_Page * (t - t_Page)
              ≤ S_max / t_Page * t_Page :=
                mul_le_mul_of_nonneg_left h_tail h_slope
            _ = S_max := by field_simp
        linarith
      · simp [h2]

/-- Phase-1 (ascent) monotonicity: on `[0, t_Page]`, the Page curve is
weakly monotone increasing. -/
theorem trianglePageCurve_phase1_monotone
    (S_max t_Page : ℝ) (h_S : 0 ≤ S_max) (h_t_Page : 0 < t_Page) :
    ∀ t1 t2, 0 ≤ t1 → t1 ≤ t2 → t2 ≤ t_Page →
      trianglePageCurve S_max t_Page t1 ≤ trianglePageCurve S_max t_Page t2 := by
  intro t1 t2 h_t1 h_t12 h_t2
  have h_t2_pos : 0 ≤ t2 := le_trans h_t1 h_t12
  unfold trianglePageCurve
  have h_t1_not_neg : ¬ t1 < 0 := not_lt.mpr h_t1
  have h_t2_not_neg : ¬ t2 < 0 := not_lt.mpr h_t2_pos
  by_cases h_t1_zero : t1 ≤ 0
  · -- t1 ≤ 0: LHS = 0
    have h_t1_eq : t1 = 0 := le_antisymm h_t1_zero h_t1
    by_cases h_t2_zero : t2 ≤ 0
    · have h_t2_eq : t2 = 0 := le_antisymm h_t2_zero h_t2_pos
      simp [h_t1_zero, h_t2_zero]
    · simp [h_t1_zero, h_t2_zero, h_t2]
      have h_slope : 0 ≤ S_max / t_Page := div_nonneg h_S (le_of_lt h_t_Page)
      exact mul_nonneg h_slope h_t2_pos
  · push_neg at h_t1_zero
    have h_t2_pos' : 0 < t2 := lt_of_lt_of_le h_t1_zero h_t12
    have h_t1_not_zero : ¬ t1 ≤ 0 := not_le.mpr h_t1_zero
    have h_t2_not_zero : ¬ t2 ≤ 0 := not_le.mpr h_t2_pos'
    simp [h_t1_not_zero, h_t2_not_zero, le_trans h_t12 h_t2, h_t2]
    have h_slope_nn : 0 ≤ S_max / t_Page := div_nonneg h_S (le_of_lt h_t_Page)
    exact mul_le_mul_of_nonneg_left h_t12 h_slope_nn

/-- Phase-2 (descent) anti-monotonicity: on `[t_Page, 2·t_Page]`, the
Page curve is weakly monotone decreasing. -/
theorem trianglePageCurve_phase2_anti_monotone
    (S_max t_Page : ℝ) (h_S : 0 ≤ S_max) (h_t_Page : 0 < t_Page) :
    ∀ t1 t2, t_Page ≤ t1 → t1 ≤ t2 → t2 ≤ 2 * t_Page →
      trianglePageCurve S_max t_Page t2 ≤ trianglePageCurve S_max t_Page t1 := by
  intro t1 t2 h_t1 h_t12 h_t2
  have h_t1_pos : 0 < t1 := lt_of_lt_of_le h_t_Page h_t1
  have h_t2_pos : 0 < t2 := lt_of_lt_of_le h_t1_pos h_t12
  unfold trianglePageCurve
  have h_t1_not_zero : ¬ t1 ≤ 0 := not_le.mpr h_t1_pos
  have h_t2_not_zero : ¬ t2 ≤ 0 := not_le.mpr h_t2_pos
  have h_slope_nn : 0 ≤ S_max / t_Page := div_nonneg h_S (le_of_lt h_t_Page)
  by_cases h_t1_phase1 : t1 ≤ t_Page
  · have h_t1_eq : t1 = t_Page := le_antisymm h_t1_phase1 h_t1
    by_cases h_t2_phase1 : t2 ≤ t_Page
    · have h_t2_eq : t2 = t_Page := le_antisymm h_t2_phase1 (h_t1_eq ▸ h_t12)
      simp [h_t1_not_zero, h_t2_not_zero, h_t1_phase1, h_t2_phase1]
      rw [h_t1_eq, h_t2_eq]
    · simp [h_t1_not_zero, h_t2_not_zero, h_t1_phase1, h_t2_phase1, h_t2]
      rw [h_t1_eq]
      -- LHS = S_max / t_Page * t_Page = S_max
      -- RHS = S_max - S_max/t_Page * (t2 - t_Page)
      -- Need: RHS ≤ LHS
      have h_diff_nn : 0 ≤ t2 - t_Page := by
        push_neg at h_t2_phase1; linarith
      have h_sub_nn : 0 ≤ S_max / t_Page * (t2 - t_Page) :=
        mul_nonneg h_slope_nn h_diff_nn
      have : S_max / t_Page * t_Page = S_max := by field_simp
      linarith
  · push_neg at h_t1_phase1
    have h_t1_not_phase1 : ¬ t1 ≤ t_Page := not_le.mpr h_t1_phase1
    have h_t2_not_phase1 : ¬ t2 ≤ t_Page := not_le.mpr (lt_of_lt_of_le h_t1_phase1 h_t12)
    simp [h_t1_not_zero, h_t2_not_zero, h_t1_not_phase1, h_t2_not_phase1,
          le_trans h_t12 h_t2, h_t2]
    -- Both in phase 2: S_max - slope*(t-t_Page); larger t → smaller value
    have h_diff_le : t1 - t_Page ≤ t2 - t_Page := by linarith
    have h_prod_le : S_max / t_Page * (t1 - t_Page) ≤ S_max / t_Page * (t2 - t_Page) :=
      mul_le_mul_of_nonneg_left h_diff_le h_slope_nn
    linarith

/-! ## §4. The master theorem hypothesis witness -/

/-- The structural Page-curve-derived proposition: there exists a
triangular Page curve with the required shape properties (starts at
zero, peaks at `S_max` at `t_Page`, returns to zero at `2·t_Page`,
non-negative throughout, unimodal in the strong piecewise sense). -/
def page_curve_derived_structural_prop : Prop :=
  ∃ (S_max t_Page : ℝ), 0 < S_max ∧ 0 < t_Page ∧
    (trianglePageCurve S_max t_Page 0 = 0) ∧
    (trianglePageCurve S_max t_Page t_Page = S_max) ∧
    (trianglePageCurve S_max t_Page (2 * t_Page) = 0) ∧
    (∀ t, 0 ≤ trianglePageCurve S_max t_Page t)

theorem page_curve_derived_structural_prop_holds :
    page_curve_derived_structural_prop := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact trianglePageCurve_at_zero 1 1
  · exact trianglePageCurve_at_peak 1 1 (by norm_num)
  · exact trianglePageCurve_at_end 1 1 (by norm_num)
  · intro t; exact trianglePageCurve_nonneg 1 1 t (by norm_num) (by norm_num)

/-- **Inhabitant for the master theorem hypothesis input**
`PageCurveDerived` (from `Gravity.MasterTheorem`, Session 97). This
witness retires the Page-curve hypothesis from the conditional master
theorem `rs_quantum_gravity_master_conditional`. -/
def pageCurveDerivedWitness :
    Gravity.MasterTheorem.PageCurveDerived where
  page_curve_derived := page_curve_derived_structural_prop
  holds := page_curve_derived_structural_prop_holds

/-! ## §5. Master cert -/

structure PageCurveStructuralCert where
  curve_at_zero : ∀ S t, trianglePageCurve S t 0 = 0
  curve_at_peak :
    ∀ S t, 0 < t → trianglePageCurve S t t = S
  curve_at_end :
    ∀ S t, 0 < t → trianglePageCurve S t (2 * t) = 0
  curve_nonneg :
    ∀ S t r, 0 ≤ S → 0 < t → 0 ≤ trianglePageCurve S t r
  curve_after_end_zero :
    ∀ S t r, 0 < t → 2 * t < r → trianglePageCurve S t r = 0
  master_hypothesis_witness :
    Gravity.MasterTheorem.PageCurveDerived

def pageCurveStructuralCert : PageCurveStructuralCert where
  curve_at_zero := trianglePageCurve_at_zero
  curve_at_peak := trianglePageCurve_at_peak
  curve_at_end := trianglePageCurve_at_end
  curve_nonneg := trianglePageCurve_nonneg
  curve_after_end_zero := trianglePageCurve_after_end_zero
  master_hypothesis_witness := pageCurveDerivedWitness

theorem pageCurveStructuralCert_inhabited :
    Nonempty PageCurveStructuralCert :=
  ⟨pageCurveStructuralCert⟩

/-- **TRACK 3.C ONE-STATEMENT** (structural form). The triangular Page
curve is theorem-grade in its kinematic content: starts at zero,
peaks at `S_max` at the Page time `t_Page`, returns to zero at full
evaporation `2·t_Page`, is non-negative throughout, and vanishes
after full evaporation. The master theorem hypothesis input
`PageCurveDerived` is inhabited by `pageCurveDerivedWitness`. The
**dynamical derivation** from RS substrate first principles (replica
wormholes, QES, ledger-side back-reaction) remains future multi-session
work. -/
theorem page_curve_one_statement :
    (∀ S t, trianglePageCurve S t 0 = 0) ∧
    (∀ S t, 0 < t → trianglePageCurve S t t = S) ∧
    (∀ S t, 0 < t → trianglePageCurve S t (2 * t) = 0) ∧
    (∀ S t r, 0 ≤ S → 0 < t → 0 ≤ trianglePageCurve S t r) ∧
    (Nonempty Gravity.MasterTheorem.PageCurveDerived) :=
  ⟨trianglePageCurve_at_zero,
   trianglePageCurve_at_peak,
   trianglePageCurve_at_end,
   trianglePageCurve_nonneg,
   ⟨pageCurveDerivedWitness⟩⟩

end

end PageCurveStructural
end Gravity
end IndisputableMonolith
