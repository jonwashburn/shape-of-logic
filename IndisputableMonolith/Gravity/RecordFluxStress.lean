import IndisputableMonolith.Gravity.ClausiusEinsteinBridge
import IndisputableMonolith.Holography.LocalRecognitionHorizonCut

/-!
# Record-flux event stress (probe-independent)

This module constructs one probe-independent symmetric stress-like matrix from
signed exterior cut-channel events and an explicit MODEL covector assignment.
Its quadratic contraction is proved for every probe of that fixed matrix.

Honesty tags:

* covector assignment `p` is an explicit MODEL interface;
* signed channel weights are derived from posted cut records;
* this module does **not** claim continuum stress-energy, Unruh, Ricci,
  focusing, all-null equality, EFE, or C-gap1 closure.

Anti-tautology: the stress is defined once from `(w, p)` and then contracted;
there is no `∀ k, ∃ T(k)` interface and no structure field storing a target
equality.
-/

noncomputable section

namespace IndisputableMonolith
namespace Gravity
namespace RecordFluxStress

open ClausiusEinsteinBridge
open Holography.LocalRecognitionHorizonCut
open Holography.RecordMonotonicity

/--
Probe-independent event stress: the sum of weighted outer products of the
assigned covectors.  Defined componentwise so the matrix is fixed before any
probe appears.
-/
def eventStress {E : Type*} [Fintype E] (w : E → ℝ) (p : E → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => ∑ e : E, w e * p e a * p e b

/-- Outer-product summands are symmetric, hence so is `eventStress`. -/
theorem eventStress_symmetric {E : Type*} [Fintype E]
    (w : E → ℝ) (p : E → Fin 4 → ℝ) :
    Symmetric4 (eventStress w p) := by
  intro i j
  simp only [eventStress]
  refine Finset.sum_congr rfl fun e _ => by ring

private lemma sum_mul_sq (q k : Fin 4 → ℝ) (w : ℝ) :
    (∑ i, ∑ j, w * q i * q j * k i * k j) =
      w * (∑ μ, q μ * k μ) ^ 2 := by
  have h1 :
      (∑ i, ∑ j, w * q i * q j * k i * k j) =
        ∑ i, ∑ j, (w * (q i * k i)) * (q j * k j) := by
    refine Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  have h2 :
      (∑ i, ∑ j, (w * (q i * k i)) * (q j * k j)) =
        ∑ i, (w * (q i * k i)) * ∑ j, q j * k j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum]
  rw [h2, ← Finset.sum_mul]
  have h3 :
      (∑ i, w * (q i * k i)) = w * ∑ i, q i * k i := by
    simp only [Finset.mul_sum]
  rw [h3]
  ring

/--
Quadratic contraction of the fixed event stress against an arbitrary probe.
The stress is constructed from `(w, p)` before `k` appears.
-/
theorem quadContr_eventStress {E : Type*} [Fintype E]
    (w : E → ℝ) (p : E → Fin 4 → ℝ) (k : Fin 4 → ℝ) :
    quadContr (eventStress w p) k =
      ∑ e : E, w e * (∑ μ, p e μ * k μ) ^ 2 := by
  unfold quadContr eventStress
  have hpull (i j : Fin 4) :
      (∑ e : E, w e * p e i * p e j) * k i * k j =
        ∑ e : E, w e * p e i * p e j * k i * k j := by
    rw [mul_assoc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp_rw [hpull]
  have hinner (i : Fin 4) :
      (∑ j, ∑ e : E, w e * p e i * p e j * k i * k j) =
        ∑ e : E, ∑ j, w e * p e i * p e j * k i * k j :=
    Finset.sum_comm
  simp_rw [hinner]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => sum_mul_sq (p e) k (w e)

/-- Zero covectors force zero event stress (load-bearing decoy). -/
theorem eventStress_zero_of_covector_zero {E : Type*} [Fintype E]
    (w : E → ℝ) :
    eventStress w (fun _ _ => (0 : ℝ)) = 0 := by
  ext i j
  simp [eventStress]

/-- Zero covectors force zero quadratic contraction for every probe. -/
theorem quadContr_eventStress_zero_of_covector_zero {E : Type*} [Fintype E]
    (w : E → ℝ) (k : Fin 4 → ℝ) :
    quadContr (eventStress w (fun _ _ => (0 : ℝ))) k = 0 := by
  rw [quadContr_eventStress]
  simp

/-- Exterior cut channels: exterior-private bits plus seam bits. -/
abbrev ExteriorCutChannel (a s : ℕ) := Fin a ⊕ Fin s

/-- Posted Boolean bit on one exterior cut channel. -/
def channelBitReadout {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c : LocalCut H) (ch : ExteriorCutChannel a s) : Bool :=
  match ch with
  | Sum.inl i => bitReadout (c.cfg.1 i)
  | Sum.inr j => bitReadout (c.cfg.2.1 j)

/-- Signed integer channel delta from cut `c` to cut `c'`. -/
def channelDeltaZ {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) (ch : ExteriorCutChannel a s) : ℤ :=
  (if channelBitReadout c' ch then (1 : ℤ) else 0) -
    (if channelBitReadout c ch then 1 else 0)

/-- Real channel weight used by the event-stress construction. -/
def channelDelta {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) (ch : ExteriorCutChannel a s) : ℝ :=
  (channelDeltaZ c c' ch : ℝ)

/--
Cut event stress: one fixed symmetric matrix from signed exterior channel
weights and an explicit MODEL covector assignment.
-/
def cutEventStress {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) (p : ExteriorCutChannel a s → Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  eventStress (channelDelta c c') p

theorem cutEventStress_symmetric {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) (p : ExteriorCutChannel a s → Fin 4 → ℝ) :
    Symmetric4 (cutEventStress c c' p) :=
  eventStress_symmetric _ _

theorem quadContr_cutEventStress {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) (p : ExteriorCutChannel a s → Fin 4 → ℝ)
    (k : Fin 4 → ℝ) :
    quadContr (cutEventStress c c' p) k =
      ∑ ch : ExteriorCutChannel a s,
        channelDelta c c' ch * (∑ μ, p ch μ * k μ) ^ 2 :=
  quadContr_eventStress _ _ _

/-- Zero cut-channel covectors force zero cut event stress. -/
theorem cutEventStress_zero_of_covector_zero {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) :
    cutEventStress c c' (fun _ _ => (0 : ℝ)) = 0 :=
  eventStress_zero_of_covector_zero _

/--
Non-tautology witness: a single event with unit weight and a nonzero covector
produces a nonzero stress matrix.
-/
theorem eventStress_ne_zero_of_unit_channel :
    eventStress (fun _ : Fin 1 => (1 : ℝ))
        (fun _ μ => if μ = (0 : Fin 4) then (1 : ℝ) else 0) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h (0 : Fin 4)) (0 : Fin 4)
  simp [eventStress] at h00

/-! ## Heat ↔ channel-delta bridge -/

private def bitDelta (b b' : Bool) : ℤ :=
  (if b' then (1 : ℤ) else 0) - (if b then 1 else 0)

private lemma recordFlux_eq_sum_bitDelta (r r' : List Bool) :
    recordFlux r r' = (List.zipWith bitDelta r r').sum :=
  rfl

private lemma exteriorRecord_as_channels {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa} (c : LocalCut H) :
    exteriorRecord c =
      List.ofFn (fun i : Fin a => channelBitReadout c (Sum.inl i)) ++
        List.ofFn (fun j : Fin s => channelBitReadout c (Sum.inr j)) :=
  rfl

private lemma zipWith_bitDelta_ofFn {n : ℕ} (f g : Fin n → Bool) :
    List.zipWith bitDelta (List.ofFn f) (List.ofFn g) =
      List.ofFn fun i => bitDelta (f i) (g i) := by
  apply List.ext_getElem
  · simp [List.length_zipWith, List.length_ofFn]
  · intro i h₁ h₂
    have hi : i < n := by
      simpa [List.length_ofFn] using h₂
    simp [List.getElem_zipWith, List.getElem_ofFn]

private lemma sum_ofFn_eq_sum {n : ℕ} (f : Fin n → ℤ) :
    (List.ofFn f).sum = ∑ i : Fin n, f i := by
  simp [List.sum_ofFn]

/--
Posted exterior heat equals the sum of signed exterior channel deltas.
This links the new channel weights to the committed cut heat.
-/
theorem exteriorStepHeat_eq_sum_channelDeltaZ {a s b r : ℕ} {kappa : ℝ}
    {H : LocalHorizonContext a s b r kappa}
    (c c' : LocalCut H) :
    exteriorStepHeat c c' = ∑ ch : ExteriorCutChannel a s, channelDeltaZ c c' ch := by
  unfold exteriorStepHeat
  rw [recordFlux_eq_sum_bitDelta, exteriorRecord_as_channels c, exteriorRecord_as_channels c']
  set fA := fun i : Fin a => channelBitReadout c (Sum.inl i)
  set fS := fun j : Fin s => channelBitReadout c (Sum.inr j)
  set gA := fun i : Fin a => channelBitReadout c' (Sum.inl i)
  set gS := fun j : Fin s => channelBitReadout c' (Sum.inr j)
  have hlen : (List.ofFn fA).length = (List.ofFn gA).length := by
    simp [List.length_ofFn]
  rw [List.zipWith_append (f := bitDelta) hlen]
  rw [zipWith_bitDelta_ofFn fA gA, zipWith_bitDelta_ofFn fS gS, List.sum_append]
  rw [sum_ofFn_eq_sum, sum_ofFn_eq_sum, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [channelDeltaZ, bitDelta, fA, gA, channelBitReadout]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [channelDeltaZ, bitDelta, fS, gS, channelBitReadout]

end RecordFluxStress
end Gravity
end IndisputableMonolith
