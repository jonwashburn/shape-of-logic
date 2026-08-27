import IndisputableMonolith.Cost
import IndisputableMonolith.Constants
import IndisputableMonolith.Foundation.PhiForcingDerived
import IndisputableMonolith.Foundation.PublicSpine.SelectedScaleClosure

/-!
# PlasticVsAdjacencyMetered — Part I Test B (growth/debt meter gate)

FROZEN 2026-07-23 (no post-hoc tuning):
MeteredLatency(r, k) := (k : ℝ) * Cost.Jcost r
  + ∑_{t=0}^{k-1} Cost.Jcost (r^t)
where k = first closing step, r = ratio forced by that short closure.
Common horizon family: evaluate each schedule at its own first-close k, then
compare under the same functional form (commensurate: both past their first
close; no coefficient tuning).
Adjacent schedule: k=2, closure L2=L0+L1 ⇒ r=φ
Plastic schedule: k=3, closure L3=L0+L1 ⇒ r=ρ with ρ>0, ρ^3=ρ+1, ρ≠φ
Constructor of MeteredLatency must NOT mention "adjacent", Fibonacci coeffs, or index-2.

Honest computation (this module): the posting term already favors the plastic
root (ρ < φ and Jcost increasing on (1,∞)); the debt sum does **not** reverse
the inequality. Hence FAIL-B: `plasticMeter ≤ adjacentMeter`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace PlasticVsAdjacencyMetered

open Classical
open BigOperators
open Constants
open Cost
open PhiForcingDerived
open SelectedScaleClosure

noncomputable section

/-! ## Plastic root -/

/-- Plastic-style cubic short-closure root, distinct from φ. -/
theorem exists_plastic_root :
    ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1 :=
  exists_plastic_root_ne_phi

/-- Concrete interval containing a plastic root: `1.3 ≤ ρ ≤ 1.325`.
Used only for decimal comparison bounds (not a tuned coefficient). -/
theorem exists_plastic_root_in_interval :
    ∃ r : ℝ,
      (13 / 10 : ℝ) ≤ r ∧ r ≤ (53 / 40 : ℝ) ∧ r ^ 3 = r + 1 ∧ r ≠ phi := by
  let f : ℝ → ℝ := fun x => x ^ 3 - x - 1
  have hf : Continuous f := by fun_prop
  have hlo : (13 / 10 : ℝ) ≤ (53 / 40 : ℝ) := by norm_num
  have hroot : ∃ c ∈ Set.Icc (13 / 10 : ℝ) (53 / 40), f c = 0 := by
    refine intermediate_value_Icc hlo hf.continuousOn ?_
    change (0 : ℝ) ∈ Set.Icc (f (13 / 10)) (f (53 / 40))
    simp only [f]
    constructor <;> norm_num
  obtain ⟨r, hrI, hr0⟩ := hroot
  have hreq : r ^ 3 = r + 1 := by
    have : r ^ 3 - r - 1 = 0 := hr0
    linarith
  have hrne : r ≠ phi := by
    intro hφ
    have hφlo : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
    have : (53 / 40 : ℝ) < (1.61 : ℝ) := by norm_num
    linarith [hrI.2, hφlo, hφ]
  exact ⟨r, hrI.1, hrI.2, hreq, hrne⟩

/-- Chosen plastic root for the meter comparison (any root in the interval). -/
noncomputable def plasticRoot : ℝ :=
  Classical.choose exists_plastic_root_in_interval

lemma plasticRoot_spec :
    (13 / 10 : ℝ) ≤ plasticRoot ∧
      plasticRoot ≤ (53 / 40 : ℝ) ∧
        plasticRoot ^ 3 = plasticRoot + 1 ∧ plasticRoot ≠ phi :=
  Classical.choose_spec exists_plastic_root_in_interval

lemma plasticRoot_pos : (0 : ℝ) < plasticRoot := by
  have h := plasticRoot_spec.1
  linarith

lemma plasticRoot_ne_zero : plasticRoot ≠ 0 := ne_of_gt plasticRoot_pos

lemma plasticRoot_gt_one : (1 : ℝ) < plasticRoot := by
  have h := plasticRoot_spec.1
  linarith

lemma plasticRoot_lt_phi : plasticRoot < phi := by
  have hφlo : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
  have hhi := plasticRoot_spec.2.1
  have : (53 / 40 : ℝ) < (1.61 : ℝ) := by norm_num
  linarith

/-! ## Frozen metered-latency functional -/

/-- Frozen parameter-free meter (constructor mentions only `r`, `k`, and `Jcost`). -/
noncomputable def meteredLatency (r : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) * Jcost r + ∑ t ∈ Finset.range k, Jcost (r ^ t)

lemma meteredLatency_two (r : ℝ) :
    meteredLatency r 2 = (3 : ℝ) * Jcost r + Jcost 1 := by
  simp [meteredLatency, Finset.sum_range_succ, pow_zero, pow_one]
  ring

lemma meteredLatency_three (r : ℝ) :
    meteredLatency r 3 = (4 : ℝ) * Jcost r + Jcost (r ^ 2) + Jcost 1 := by
  simp [meteredLatency, Finset.sum_range_succ, pow_zero, pow_one]
  ring

/-- φ-schedule evaluated at its first-close horizon `k = 2`. -/
noncomputable def adjacentMeter : ℝ := meteredLatency phi 2

/-- Plastic schedule evaluated at its first-close horizon `k = 3`. -/
noncomputable def plasticMeter : ℝ := meteredLatency plasticRoot 3

lemma adjacentMeter_eq : adjacentMeter = (3 : ℝ) * Jcost phi := by
  simp [adjacentMeter, meteredLatency_two, Jcost_unit0]

lemma plasticMeter_eq :
    plasticMeter = (4 : ℝ) * Jcost plasticRoot + Jcost (plasticRoot ^ 2) := by
  simp [plasticMeter, meteredLatency_three, Jcost_unit0]

/-! ## Closed forms under the plastic cubic -/

lemma plasticRoot_inv_eq :
    plasticRoot⁻¹ = plasticRoot ^ 2 - 1 := by
  have hr := plasticRoot_spec.2.2.1
  have hmul : (plasticRoot ^ 2 - 1) * plasticRoot = 1 := by
    have : plasticRoot ^ 3 - plasticRoot = 1 := by linarith [hr]
    calc
      (plasticRoot ^ 2 - 1) * plasticRoot = plasticRoot ^ 3 - plasticRoot := by ring
      _ = 1 := this
  exact inv_eq_of_mul_eq_one_left hmul

lemma plasticRoot_sq_inv_eq :
    (plasticRoot ^ 2)⁻¹ = 1 + plasticRoot - plasticRoot ^ 2 := by
  have hr := plasticRoot_spec.2.2.1
  have hmul : (1 + plasticRoot - plasticRoot ^ 2) * plasticRoot ^ 2 = 1 := by
    have h4 : plasticRoot ^ 4 = plasticRoot ^ 2 + plasticRoot := by
      calc
        plasticRoot ^ 4 = plasticRoot * plasticRoot ^ 3 := by ring
        _ = plasticRoot * (plasticRoot + 1) := by rw [hr]
        _ = plasticRoot ^ 2 + plasticRoot := by ring
    calc
      (1 + plasticRoot - plasticRoot ^ 2) * plasticRoot ^ 2
          = plasticRoot ^ 2 + plasticRoot ^ 3 - plasticRoot ^ 4 := by ring
      _ = plasticRoot ^ 2 + (plasticRoot + 1) - (plasticRoot ^ 2 + plasticRoot) := by
            rw [hr, h4]
      _ = 1 := by ring
  exact inv_eq_of_mul_eq_one_left hmul

lemma Jcost_plasticRoot :
    Jcost plasticRoot = (plasticRoot ^ 2 + plasticRoot - 3) / 2 := by
  unfold Jcost
  rw [plasticRoot_inv_eq]
  ring

lemma Jcost_plasticRoot_sq :
    Jcost (plasticRoot ^ 2) = (plasticRoot - 1) / 2 := by
  unfold Jcost
  rw [plasticRoot_sq_inv_eq]
  ring

lemma plasticMeter_closed_form :
    plasticMeter =
      (2 : ℝ) * plasticRoot ^ 2 + (5 / 2) * plasticRoot - 13 / 2 := by
  rw [plasticMeter_eq, Jcost_plasticRoot, Jcost_plasticRoot_sq]
  ring

lemma adjacentMeter_closed_form :
    adjacentMeter = (3 : ℝ) * phi - 9 / 2 := by
  rw [adjacentMeter_eq, Jcost_phi_val]
  ring

/-! ## FAIL-B comparison -/

lemma plasticMeter_le_decimal :
    plasticMeter ≤ (259 / 800 : ℝ) := by
  -- At ρ = 53/40 = 1.325 the closed form equals 259/800 = 0.32375.
  have hform := plasticMeter_closed_form
  have hx : plasticRoot ≤ (53 / 40 : ℝ) := plasticRoot_spec.2.1
  set a : ℝ := 53 / 40
  have hdiff :
      (2 : ℝ) * a ^ 2 + (5 / 2) * a - 13 / 2 -
          ((2 : ℝ) * plasticRoot ^ 2 + (5 / 2) * plasticRoot - 13 / 2) =
        (a - plasticRoot) * (2 * (a + plasticRoot) + 5 / 2) := by
    ring
  have hnonneg :
      (0 : ℝ) ≤
        (2 : ℝ) * a ^ 2 + (5 / 2) * a - 13 / 2 -
          ((2 : ℝ) * plasticRoot ^ 2 + (5 / 2) * plasticRoot - 13 / 2) := by
    rw [hdiff]
    have h1 : (0 : ℝ) ≤ a - plasticRoot := sub_nonneg.mpr hx
    have h2 : (0 : ℝ) ≤ 2 * (a + plasticRoot) + 5 / 2 := by
      have : (0 : ℝ) ≤ plasticRoot := le_of_lt plasticRoot_pos
      have ha : (0 : ℝ) ≤ a := by norm_num [a]
      linarith
    exact mul_nonneg h1 h2
  have hval :
      (2 : ℝ) * a ^ 2 + (5 / 2) * a - 13 / 2 = (259 / 800 : ℝ) := by
    norm_num [a]
  linarith [hform, hnonneg, hval]

lemma adjacentMeter_gt_decimal :
    (33 / 100 : ℝ) < adjacentMeter := by
  rw [adjacentMeter_closed_form]
  have hφ : (1.61 : ℝ) < phi := phi_gt_onePointSixOne
  -- 3*1.61 - 9/2 = 0.33 = 33/100
  linarith

/-- FAIL-B: plastic schedule is not strictly more expensive; meter does not
select the φ/adjacent first-close over plastic. -/
theorem plasticMeter_le_adjacentMeter : plasticMeter ≤ adjacentMeter := by
  have hP := plasticMeter_le_decimal
  have hA := adjacentMeter_gt_decimal
  have : (259 / 800 : ℝ) < (33 / 100 : ℝ) := by norm_num
  linarith

/-! ## Reverse witness (FAIL-B) -/

/-- Named selection predicate: frozen meter strictly prefers the φ-schedule. -/
def MeteredSelectsAdjacent : Prop := adjacentMeter < plasticMeter

theorem metered_does_not_select_adjacent : ¬ MeteredSelectsAdjacent := by
  intro h
  exact (not_lt_of_ge plasticMeter_le_adjacentMeter) h

/-- Geometric adjacency/`isClosed` holds at φ. -/
theorem phi_adjacency_isClosed :
    ∃ S : GeometricScaleSequence, S.isClosed ∧ S.ratio = phi := by
  refine ⟨⟨phi, phi_pos, phi_ne_one⟩, ?_, rfl⟩
  unfold GeometricScaleSequence.isClosed ledgerCompose GeometricScaleSequence.scale
  simp only [pow_zero, pow_one]
  have h : phi ^ 2 = phi + 1 := phi_sq_eq
  -- need 1 + phi = phi^2
  linarith [h]

/-- Reverse witness: adjacency/`isClosed` at φ holds, while
`MeteredSelectsAdjacent` fails under the frozen meter. -/
theorem reverse_witness_adjacency_without_metered_select :
    (∃ S : GeometricScaleSequence, S.isClosed ∧ S.ratio = phi) ∧
      ¬ MeteredSelectsAdjacent :=
  ⟨phi_adjacency_isClosed, metered_does_not_select_adjacent⟩

/-! ## Gate certificate -/

inductive GateBVerdict
  | pass
  | fail
  | noDecision
  deriving DecidableEq, Repr

structure PlasticVsAdjacencyMeteredCert where
  -- Absent by design (was typed `True`, so disciplined nothing):
  -- functional_frozen (metatheoretic protocol claim that the meter is FROZEN
  -- 2026-07-23; the freeze lives in the module docstring, not a kernel Prop).
  plastic_root : ∃ r : ℝ, 0 < r ∧ r ≠ phi ∧ r ^ 3 = r + 1
  comparison : plasticMeter ≤ adjacentMeter
  verdict : GateBVerdict

/-- Compiled Test B receipt: FAIL (meter does not select adjacent over plastic). -/
noncomputable def plasticVsAdjacencyMeteredCert : PlasticVsAdjacencyMeteredCert where
  plastic_root := exists_plastic_root
  comparison := plasticMeter_le_adjacentMeter
  verdict := GateBVerdict.fail

theorem gateB_verdict_is_fail :
    plasticVsAdjacencyMeteredCert.verdict = GateBVerdict.fail :=
  rfl

end
end PlasticVsAdjacencyMetered
end PublicSpine
end Foundation
end IndisputableMonolith
