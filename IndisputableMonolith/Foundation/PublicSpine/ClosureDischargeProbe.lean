import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.HierarchyDynamics
import IndisputableMonolith.Foundation.HierarchyEmergence
import IndisputableMonolith.Foundation.HierarchyForcing
import IndisputableMonolith.Foundation.HierarchyRealizationFromScale
import IndisputableMonolith.Foundation.HierarchyRealizationObstruction
import IndisputableMonolith.Foundation.PostingExtensivity
import IndisputableMonolith.Foundation.PublicSpine.SelectedClosureNecessity
import IndisputableMonolith.Foundation.UniversalForcing.ReciprocalGenerator
import IndisputableMonolith.PhiSupport.Lemmas

/-!
# ClosureDischargeProbe — Lane B deep discovery (Probe B)

Goal: discharge (or honestly wall) the open half of
`SelectedClosureNecessity`: derive additive scale posting and locality
from earlier Recognition structure, rather than disclose them.

## Inventory (proves vs assumes)

| Route | Decl / file | Status |
|---|---|---|
| Bare COF → additive | `closedFramework_does_not_force_additive_posting` | NEGATIVE (THEOREM obstruction) |
| Cond P_closure → φ | `SelectedClosureNecessity` / `premises_force_phi` | PROVES under disclosed locality+min |
| Posting Π / d'Alembert | `posting_dalembert` | PROVES identity; does **not** force `L2=L1+L0` |
| `closure_forces_additive` | `PostingExtensivity` | PACKAGING: takes closure as hyp |
| `posting_extensivity_forces_phi` | same | ASSUMES additive closure |
| RealizedClosedScale → additive | `additive_posting_of_realized_closed_scale` | PROVES from `scales.isClosed` (earlier closure) |
| RealizedHierarchy → φ | `bridge_T5_T6_internal` | ASSUMES `additive_posting` field |
| Recognition-work → size add | `recognition_work_posting_size_additive` (UFC) | PROVES additivity of κ under join+indep |
| Seed compose = L0⋈L1 | `seed_event_composes` / `AdditiveSeedPostingModel` | ASSUMED model field |
| Zero-param ⇒ (1,1) | `additive_composition_is_minimal` | PROVES under `max=1` **posture** |
| ReciprocalGenerator | `recipShift_fixed_iff` | PROVES uniqueness of φ as FP of `1+1/x`; not least-cost selection of the map |
| Folding ladder | `PhiLadderForcingFromChain` | ASSUMES `RealizedHierarchy` (hence additive) |
| Non-minimal exclusion | **this file** | PROVES: max(a,b)≥2 ⇒ char root > φ; least J among family |

## Strongest honest chain

Recognition-work cost additivity (UFC) + seed compose interpretation
→ canonical seed-size law `L2 = L0+L1` → (with uniform ladder) φ.

Still missing for full discharge from bare COF / T5 alone:
1. levels = recognition-work costs of orbit events;
2. level-2 event is the join of level-0 and level-1 seeds;
3. locality of the recurrence (binary, not higher-order);
4. (optional upgrade) least-growth / least-J among integer pairs — **proved here**,
   converting zero-param minimality from posture to least-cost theorem
   *inside the local binary integer family*.

## Attempt

Concrete target (a): non-minimal exclusion + least-J-cost among
`L₂ = a L₁ + b L₀` with `a,b ∈ ℕ₊`.
Target (b) least-cost self-composition among a broader admissible map family:
stated as a named OPEN gap (`LeastCostSelfCompositionGap`).
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace ClosureDischargeProbe

open HierarchyEmergence
open HierarchyDynamics
open HierarchyForcing
open HierarchyRealizationFromScale
open HierarchyRealizationObstruction
open PostingExtensivity
open ClosedFramework
open Constants
open Cost
open UniversalForcing.ReciprocalGenerator

/-! ## Step A: characteristic equation of a local binary integer recurrence -/

/-- On a uniform ladder, `L₂ = a L₁ + b L₀` forces the characteristic
equation `σ² = a σ + b`. -/
theorem general_recurrence_char_eq
    (L : UniformScaleLadder) (a b : ℕ)
    (hrec : L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0) :
    L.ratio ^ 2 = (a : ℝ) * L.ratio + (b : ℝ) := by
  have h0 : L.levels 0 ≠ 0 := ne_of_gt (L.levels_pos 0)
  have h1 : L.levels 1 = L.ratio * L.levels 0 := L.uniform_scaling 0
  have h2 : L.levels 2 = L.ratio * L.levels 1 := L.uniform_scaling 1
  have h_sq : L.levels 2 = L.ratio ^ 2 * L.levels 0 := by
    rw [h2, h1]; ring
  have h_rhs : L.levels 2 = ((a : ℝ) * L.ratio + (b : ℝ)) * L.levels 0 := by
    rw [hrec, h1]; ring
  have h_mul :
      (L.ratio ^ 2 - ((a : ℝ) * L.ratio + (b : ℝ))) * L.levels 0 = 0 := by
    calc
      (L.ratio ^ 2 - ((a : ℝ) * L.ratio + (b : ℝ))) * L.levels 0
          = L.ratio ^ 2 * L.levels 0 -
              ((a : ℝ) * L.ratio + (b : ℝ)) * L.levels 0 := by ring
      _ = L.levels 2 - L.levels 2 := by rw [← h_sq, h_rhs]
      _ = 0 := by ring
  rcases mul_eq_zero.mp h_mul with hzero | hsize
  · exact sub_eq_zero.mp hzero
  · exact (h0 hsize).elim

/-! ## Step B: non-minimal pairs force growth strictly above φ -/

/-- Evaluation identity: `φ² - aφ - b = φ(1-a) + (1-b)`. -/
theorem phi_char_residual (a b : ℕ) :
    phi ^ 2 - (a : ℝ) * phi - (b : ℝ) =
      phi * (1 - (a : ℝ)) + (1 - (b : ℝ)) := by
  have hsq := phi_sq_eq
  linear_combination hsq

/-- If `max(a,b) ≥ 2` with positive integer coefficients, then
`φ² < a φ + b` (φ lies strictly below the positive characteristic root). -/
theorem nonminimal_phi_below_char (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hmax : 2 ≤ max a b) :
    phi ^ 2 < (a : ℝ) * phi + (b : ℝ) := by
  have hres := phi_char_residual a b
  have hphi : (1 : ℝ) < phi := by
    linarith [phi_gt_onePointFive]
  -- Split on which coefficient is large.
  have hcases : 2 ≤ a ∨ 2 ≤ b := by
    cases' le_max_iff.mp hmax with ha2 hb2
    · exact Or.inl ha2
    · exact Or.inr hb2
  have hneg : phi ^ 2 - (a : ℝ) * phi - (b : ℝ) < 0 := by
    rw [hres]
    rcases hcases with ha2 | hb2
    · -- a ≥ 2 ⇒ φ(1-a) ≤ -φ < 0 and (1-b) ≤ 0
      have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
      have hterm1 : phi * (1 - (a : ℝ)) ≤ phi * (1 - 2) := by
        have : (1 : ℝ) - (a : ℝ) ≤ 1 - 2 := by linarith
        exact mul_le_mul_of_nonneg_left this (le_of_lt (lt_trans one_pos hphi))
      have hterm2 : (1 : ℝ) - (b : ℝ) ≤ 0 := by
        have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        linarith
      have : phi * (1 - (a : ℝ)) + (1 - (b : ℝ)) ≤ phi * (-1) + 0 := by
        linarith [hterm1, hterm2]
      have : phi * (1 - (a : ℝ)) + (1 - (b : ℝ)) ≤ -phi := by
        simpa [mul_neg, mul_one] using this
      linarith [hphi]
    · -- b ≥ 2, a ≥ 1: residual ≤ 1-b ≤ -1 < 0 (even if a=1)
      have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
      have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hterm1 : phi * (1 - (a : ℝ)) ≤ 0 := by
        have : (1 : ℝ) - (a : ℝ) ≤ 0 := by linarith
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (lt_trans one_pos hphi)) this
      have hterm2 : (1 : ℝ) - (b : ℝ) ≤ -1 := by linarith
      linarith
  linarith

/-- **Non-minimal exclusion (growth)**: on a uniform ladder, a local binary
integer recurrence with `max(a,b) ≥ 2` forces scale ratio strictly larger
than φ. -/
theorem nonminimal_recurrence_ratio_gt_phi
    (L : UniformScaleLadder) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hrec : L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0)
    (hmax : 2 ≤ max a b) :
    phi < L.ratio := by
  have hchar := general_recurrence_char_eq L a b hrec
  have hphi_lt : phi ^ 2 < (a : ℝ) * phi + (b : ℝ) :=
    nonminimal_phi_below_char a b ha hb hmax
  -- Contradiction if σ ≤ φ: x ↦ x² is increasing on [1,∞).
  by_contra hle
  push_neg at hle
  have hσ1 : (1 : ℝ) < L.ratio := L.ratio_gt_one
  have hσ0 : (0 : ℝ) < L.ratio := lt_trans one_pos hσ1
  have hsq_le : L.ratio ^ 2 ≤ phi ^ 2 := by
    have : L.ratio ≤ phi := hle
    exact sq_le_sq' (by linarith) this
  -- Lower-bound σ² from the large coefficient.
  have hcases : 2 ≤ a ∨ 2 ≤ b := by
    cases' le_max_iff.mp hmax with ha2 hb2
    · exact Or.inl ha2
    · exact Or.inr hb2
  rcases hcases with ha2 | hb2
  · -- a ≥ 2, b ≥ 1 ⇒ σ² = aσ+b ≥ 2σ+1
    have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hlow : (2 : ℝ) * L.ratio + 1 ≤ L.ratio ^ 2 := by
      have : (2 : ℝ) * L.ratio + 1 ≤ (a : ℝ) * L.ratio + (b : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr haR) (le_of_lt hσ0)]
      linarith [hchar]
    -- Then 2σ+1 ≤ σ² ≤ φ² = φ+1 ⇒ 2σ ≤ φ ⇒ σ ≤ φ/2 < 1
    have hφsq : phi ^ 2 = phi + 1 := phi_sq_eq
    have : (2 : ℝ) * L.ratio + 1 ≤ phi + 1 := by linarith [hsq_le, hφsq]
    have : (2 : ℝ) * L.ratio ≤ phi := by linarith
    have : L.ratio ≤ phi / 2 := by linarith
    have hφhalf : phi / 2 < 1 := by
      have : phi < 2 := by
        linarith [phi_lt_onePointSixTwo]
      linarith
    linarith
  · -- a ≥ 1, b ≥ 2 ⇒ σ² = aσ+b ≥ σ+2
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb2
    have hlow : L.ratio + 2 ≤ L.ratio ^ 2 := by
      have : L.ratio + 2 ≤ (a : ℝ) * L.ratio + (b : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr haR) (le_of_lt hσ0)]
      linarith [hchar]
    have hφsq : phi ^ 2 = phi + 1 := phi_sq_eq
    have : L.ratio + 2 ≤ phi + 1 := by linarith [hsq_le, hφsq]
    -- σ ≤ φ − 1 = 1/φ < 1
    have : L.ratio ≤ phi - 1 := by linarith
    have hφm1 : phi - 1 < 1 := by linarith [phi_lt_onePointSixTwo]
    linarith

/-- Unit coefficients force φ (reuses the banked bridge). -/
theorem unit_recurrence_forces_phi
    (L : UniformScaleLadder)
    (hrec : L.levels 2 =
      ((1 : ℕ) : ℝ) * L.levels 1 + ((1 : ℕ) : ℝ) * L.levels 0) :
    L.ratio = phi := by
  have hfib : L.levels 2 = L.levels 1 + L.levels 0 := by
    simpa using hrec
  have h := hierarchy_emergence_forces_phi L hfib
  simpa [PhiForcing.φ, phi] using h

/-- Among positive integer coefficient pairs, `(1,1)` is the unique pair
achieving the φ growth rate on a uniform ladder (others exceed φ). -/
theorem fibonacci_unique_minimal_growth
    (L : UniformScaleLadder) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hrec : L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0) :
    L.ratio = phi ↔ a = 1 ∧ b = 1 := by
  constructor
  · intro hφ
    by_contra hne
    have hmax : 2 ≤ max a b := other_pairs_larger a b ha hb hne
    have hgt := nonminimal_recurrence_ratio_gt_phi L a b ha hb hrec hmax
    rw [hφ] at hgt
    exact (lt_irrefl phi) hgt
  · intro ⟨ha1, hb1⟩
    subst ha1; subst hb1
    exact unit_recurrence_forces_phi L hrec

/-! ## Step C: least J-cost among the same family -/

/-- Non-minimal pairs force strictly greater recognition cost of the scale
ratio than `J(φ)`. This converts zero-parameter minimality from a posture
into a least-cost theorem *inside* the local binary integer family. -/
theorem nonminimal_recurrence_jcost_gt_phi
    (L : UniformScaleLadder) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hrec : L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0)
    (hmax : 2 ≤ max a b) :
    Jcost phi < Jcost L.ratio := by
  have hgt := nonminimal_recurrence_ratio_gt_phi L a b ha hb hrec hmax
  have hφ1 : (1 : ℝ) ≤ phi := by
    linarith [phi_gt_onePointFive]
  have hσpos : (0 : ℝ) < L.ratio := lt_trans one_pos L.ratio_gt_one
  have hφpos : (0 : ℝ) < phi := lt_trans one_pos (by linarith [phi_gt_onePointFive])
  exact Jcost_strict_mono_on_one_infty phi L.ratio hφpos hσpos hφ1 hgt

/-- Clean form: if the coefficient pair is not `(1,1)`, its ladder ratio
costs strictly more than `J(φ)`. -/
theorem non_unit_pair_strictly_costlier
    (L : UniformScaleLadder) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hrec : L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0)
    (hne : ¬ (a = 1 ∧ b = 1)) :
    Jcost phi < Jcost L.ratio :=
  nonminimal_recurrence_jcost_gt_phi L a b ha hb hrec
    (other_pairs_larger a b ha hb hne)

/-- Package: `(1,1)` is the unique least-growth / least-J local binary
integer recurrence on uniform ladders. -/
structure NonminimalExclusionCert : Prop where
  /-- Non-minimal coefficients force growth above φ. -/
  growth :
    ∀ (L : UniformScaleLadder) (a b : ℕ),
      1 ≤ a → 1 ≤ b →
      L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0 →
      2 ≤ max a b →
      phi < L.ratio
  /-- Same pairs force strictly larger J-cost than φ. -/
  jcost :
    ∀ (L : UniformScaleLadder) (a b : ℕ),
      1 ≤ a → 1 ≤ b →
      L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0 →
      ¬ (a = 1 ∧ b = 1) →
      Jcost phi < Jcost L.ratio
  /-- Unit pair realizes φ. -/
  unit_is_phi :
    ∀ (L : UniformScaleLadder),
      L.levels 2 =
          ((1 : ℕ) : ℝ) * L.levels 1 + ((1 : ℕ) : ℝ) * L.levels 0 →
      L.ratio = phi
  /-- Uniqueness of φ growth among the family. -/
  unique_growth :
    ∀ (L : UniformScaleLadder) (a b : ℕ),
      1 ≤ a → 1 ≤ b →
      L.levels 2 = (a : ℝ) * L.levels 1 + (b : ℝ) * L.levels 0 →
      (L.ratio = phi ↔ a = 1 ∧ b = 1)

theorem nonminimalExclusionCert_holds : NonminimalExclusionCert where
  growth := nonminimal_recurrence_ratio_gt_phi
  jcost := non_unit_pair_strictly_costlier
  unit_is_phi := unit_recurrence_forces_phi
  unique_growth := fibonacci_unique_minimal_growth

/-! ## Honesty: what is still OPEN for full package discharge -/

/-- Known negative: bare `ClosedObservableFramework` does not force additive
posting. Re-exported for the probe binder. -/
theorem bare_framework_obstruction :
    ∃ (F : ClosedObservableFramework) (base : F.S),
      ¬ CarriesAdditiveScalePosting F base :=
  closedFramework_does_not_force_additive_posting

/-- `PostingExtensivity.closure_forces_additive` takes closure as input
(packaging identity). Recorded so the probe cannot be misread as claiming
d'Alembert alone forces additivity. -/
theorem posting_closure_still_assumes_closure
    (levels : ℕ → ℝ) (levels_pos : ∀ k, 0 < levels k)
    (σ : ℝ) (hσ : 1 < σ)
    (uniform : ∀ k, levels (k + 1) = σ * levels k)
    (closure : levels 0 + levels 1 = levels 2) :
    levels 2 = levels 1 + levels 0 :=
  closure_forces_additive levels levels_pos σ hσ uniform closure

/-- `RealizedClosedScaleModel` derives `additive_posting` only after assuming
an earlier geometric `isClosed`. That pushes the residual one layer earlier;
it does not eliminate it. -/
theorem realized_closed_scale_additive_from_isClosed
    (F : ClosedObservableFramework) (H : RealizedClosedScaleModel F) :
    F.r (F.T^[2] H.baseState) =
      F.r (F.T^[1] H.baseState) + F.r (F.T^[0] H.baseState) :=
  HierarchyRealizationFromScale.additive_posting_of_realized_closed_scale F H

/-- ReciprocalGenerator uniqueness: φ is the unique fixed point `> 1` of
`1 + 1/x`. This is NOT a least-cost selection among maps. -/
theorem recipShift_unique_fixed_point {x : ℝ} (hx : 1 < x) :
    recipShift x = x ↔ x = phi :=
  recipShift_fixed_iff hx

/-- **OPEN GAP (target b)**: there is no theorem in the monolith that a
definable admissible family of self-composition maps is ordered by J-cost
with least element `x ↦ 1 + 1/x`.

What exists: uniqueness of the fixed point of that map (`recipShift_fixed_iff`),
and least-J among *integer binary recurrence coefficients* (this file).
What is missing: a Recognition-native admissible class `AdmissibleSelfCompose`
of maps `f : ℝ₊ → ℝ₊` with a theorem
`IsLeastJCostSelfCompose (fun x => 1 + x⁻¹)`. -/
structure LeastCostSelfCompositionGap : Prop where
  /-- Placeholder openness marker: inhabited only as documentation that the
  stronger map-family theorem is not claimed. -/
  stated : True := trivial

/-- **OPEN GAP**: locality of ledger posting (binary, not higher-order) is
still a disclosed field of `LocalBinaryRecurrence` /
`ClosureNecessityPremises`, not derived from bare COF. -/
structure LocalityDerivationGap : Prop where
  stated : True := trivial

/-- Probe binder: what this session proved vs what remains OPEN. -/
structure ClosureDischargeProbeCert : Prop where
  /-- Non-minimal exclusion + least-J inside the discrete local-binary family. -/
  nonminimal : NonminimalExclusionCert
  /-- Bare COF obstruction retained. -/
  obstruction : ∃ (F : ClosedObservableFramework) (base : F.S),
    ¬ CarriesAdditiveScalePosting F base
  /-- Reciprocal-shift uniqueness retained (not least-cost among maps). -/
  recip_unique : ∀ x : ℝ, 1 < x → (recipShift x = x ↔ x = phi)
  /-- Named OPEN: least-cost self-composition among maps. -/
  map_family_gap : LeastCostSelfCompositionGap
  /-- Named OPEN: derive locality from earlier structure. -/
  locality_gap : LocalityDerivationGap

theorem closureDischargeProbeCert_holds : ClosureDischargeProbeCert where
  nonminimal := nonminimalExclusionCert_holds
  obstruction := bare_framework_obstruction
  recip_unique := fun _ hx => recipShift_unique_fixed_point hx
  map_family_gap := {}
  locality_gap := {}

end ClosureDischargeProbe
end PublicSpine
end Foundation
end IndisputableMonolith
