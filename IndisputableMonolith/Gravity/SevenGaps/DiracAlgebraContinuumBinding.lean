import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.DiracAlgebraContinuum
import IndisputableMonolith.Gravity.SevenGaps.DynamicStructureBracketN

/-!
# Wave C2 R4 repair Steps 3–4: sampled HamDynN binding + periodic terminal

Binds the freestanding Riemann shape `sampledDynamicBracketSum` to the
genuine lattice bracket `bracket (HamDynN ·) (HamDynN ·)` after the
periodic wrap treatment, then lands the ledger terminal
`dirac_algebra_continuum_limit` for 1-periodic C¹ data.

## Wrap treatment

On `ZMod n`, site `n-1` has successor `0`. The non-periodic mesh samples
`(k+1)/n = 1` at the last cell; the periodic mesh samples `0`. For
1-periodic fields these agree, so
`periodicSampledDynamicBracketSum = sampledDynamicBracketSum`.

True structure-factor placement from `bracket_HamDynN_HamDynN` is `g` at
the left split point `j`, matching `dynamicStructureProfile q (k/n)`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace DiracAlgebraContinuumBinding

open HypersurfaceDeformation
open DynamicStructureBracketN
open DiracAlgebraContinuum
open DynamicStructureContinuumSmearing
open Filter Topology Set Finset

noncomputable section

/-! ## Step 3: sampled phase / lapse -/

/-- Sample continuum fields onto the `ZMod n` lattice at nodes `j.val / n`. -/
def sampledPhasePoint (n : ℕ) [NeZero n] (q p : ℝ → ℝ) : PhaseSpace n :=
  (fun j : ZMod n => q ((j.val : ℝ) / n), fun j : ZMod n => p ((j.val : ℝ) / n))

/-- Sample a continuum lapse onto lattice sites. -/
def sampledLapse (n : ℕ) [NeZero n] (N : ℝ → ℝ) : ZMod n → ℝ :=
  fun j => N ((j.val : ℝ) / n)

/-- Wrap-successor index on `{0,…,n-1}`: `n-1 ↦ 0`, else `k ↦ k+1`. -/
def wrapSucc (n k : ℕ) : ℕ :=
  if k + 1 = n then 0 else k + 1

/-- Periodic sampled RHS: last cell uses wrap samples at `0`, not at `1`. -/
def periodicSampledDynamicBracketSum (n : ℕ) (N M q p : ℝ → ℝ) : ℝ :=
  ∑ k ∈ range n,
    (N ((k : ℝ) / n) * M ((wrapSucc n k : ℕ) / n) -
        M ((k : ℝ) / n) * N ((wrapSucc n k : ℕ) / n)) *
      (dynamicStructureProfile q ((k : ℝ) / n) *
        (p ((wrapSucc n k : ℕ) / n) *
          (q ((wrapSucc n k : ℕ) / n) - q ((k : ℝ) / n))))

/-- Lattice bracket evaluated on continuum samples (junk `0` at `n = 0`). -/
def continuumLatticeBracket (n : ℕ) (N M q p : ℝ → ℝ) : ℝ :=
  if hn : n = 0 then 0
  else
    haveI : NeZero n := ⟨hn⟩
    bracket (HamDynN (sampledLapse n N)) (HamDynN (sampledLapse n M))
      (sampledPhasePoint n q p)

/-! ## ZMod sampling lemmas -/

private lemma zmod_val_of_lt {n k : ℕ} [NeZero n] (hk : k < n) :
    ((k : ZMod n).val : ℕ) = k :=
  ZMod.val_natCast_of_lt hk

private lemma wrapSucc_lt (n k : ℕ) [NeZero n] (hk : k < n) : wrapSucc n k < n := by
  unfold wrapSucc
  split_ifs with h
  · exact NeZero.pos n
  · exact Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) h

private lemma zmod_succ_val {n k : ℕ} [NeZero n] (hk : k < n) :
    (((k : ZMod n) + 1).val : ℕ) = wrapSucc n k := by
  unfold wrapSucc
  by_cases h : k + 1 = n
  · simp only [h, ↓reduceIte]
    have h0 : (k : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, h, ZMod.natCast_self]
    simp [h0]
  · simp only [h, ↓reduceIte]
    have hlt : k + 1 < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hk) h
    have : ((k : ZMod n) + 1) = ((k + 1 : ℕ) : ZMod n) := by
      simp [Nat.cast_succ]
    rw [this, zmod_val_of_lt hlt]

private lemma sum_zmod_eq_sum_range {n : ℕ} [NeZero n] (f : ZMod n → ℝ) :
    (∑ j : ZMod n, f j) = ∑ k ∈ range n, f (k : ZMod n) := by
  refine sum_nbij (fun j : ZMod n => j.val)
    (fun j _ => mem_range.2 j.val_lt)
    (fun _ _ _ _ h => ZMod.val_injective n h)
    (fun k hk => ⟨(k : ZMod n), mem_univ _, zmod_val_of_lt (mem_range.1 hk)⟩)
    (fun j _ => by rw [ZMod.natCast_zmod_val])

/-! ## Step 3 binding -/

/-- THEOREM. At continuum samples, the general-`n` dynamic bracket equals the
periodic sampled sum (definitional unfolding of `bracket_HamDynN_HamDynN`). -/
theorem bracket_HamDynN_eq_periodicSampled
    (n : ℕ) [NeZero n] (N M q p : ℝ → ℝ) :
    bracket (HamDynN (sampledLapse n N)) (HamDynN (sampledLapse n M))
        (sampledPhasePoint n q p)
      = periodicSampledDynamicBracketSum n N M q p := by
  rw [bracket_HamDynN_HamDynN]
  simp only [sampledLapse, sampledPhasePoint, periodicSampledDynamicBracketSum,
    dynamicStructureProfile]
  rw [sum_zmod_eq_sum_range]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := mem_range.1 hk
  have hv : ((k : ZMod n).val : ℕ) = k := zmod_val_of_lt hk'
  have hs : (((k : ZMod n) + 1).val : ℕ) = wrapSucc n k := zmod_succ_val hk'
  simp only [hv, hs, pow_two]

theorem continuumLatticeBracket_eq_periodic
    (n : ℕ) (N M q p : ℝ → ℝ) :
    continuumLatticeBracket n N M q p
      = periodicSampledDynamicBracketSum n N M q p := by
  unfold continuumLatticeBracket
  split_ifs with hn
  · subst hn
    simp [periodicSampledDynamicBracketSum]
  · haveI : NeZero n := ⟨hn⟩
    exact bracket_HamDynN_eq_periodicSampled (n := n) N M q p

/-! ## Step 4: periodicity equates wrap and non-wrap meshes -/

/-- 1-periodic real function on the circle of length 1. -/
def Periodic1 (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, f (t + 1) = f t

theorem Periodic1.eval_one (f : ℝ → ℝ) (hf : Periodic1 f) : f 1 = f 0 := by
  simpa using hf 0

private lemma wrapSucc_eq_succ_or_zero (n k : ℕ) :
    wrapSucc n k = k + 1 ∨ (k + 1 = n ∧ wrapSucc n k = 0) := by
  unfold wrapSucc
  by_cases h : k + 1 = n
  · exact Or.inr ⟨h, by simp [h]⟩
  · exact Or.inl (by simp [h])

/-- THEOREM. For 1-periodic data, the wrap mesh equals the non-periodic mesh
(last cell: samples at `1` equal samples at `0`). -/
theorem periodicSampled_eq_sampled_of_periodic
    (n : ℕ) (N M q p : ℝ → ℝ)
    (hN : Periodic1 N) (hM : Periodic1 M) (hq : Periodic1 q) (hp : Periodic1 p) :
    periodicSampledDynamicBracketSum n N M q p
      = sampledDynamicBracketSum n N M q p := by
  unfold periodicSampledDynamicBracketSum sampledDynamicBracketSum
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := mem_range.1 hk
  rcases wrapSucc_eq_succ_or_zero n k with h | ⟨hEq, hW⟩
  · simp [h]
  · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk')
    have hdiv : (n : ℝ) / n = 1 := by field_simp
    have hN1 : N ((n : ℝ) / n) = N 0 := by rw [hdiv]; exact Periodic1.eval_one N hN
    have hM1 : M ((n : ℝ) / n) = M 0 := by rw [hdiv]; exact Periodic1.eval_one M hM
    have hq1 : q ((n : ℝ) / n) = q 0 := by rw [hdiv]; exact Periodic1.eval_one q hq
    have hp1 : p ((n : ℝ) / n) = p 0 := by rw [hdiv]; exact Periodic1.eval_one p hp
    simp [hW, hEq, hN1, hM1, hq1, hp1, zero_div]

/-- Scaled lattice bracket equals scaled freestanding shape under periodicity. -/
theorem scaled_continuumLatticeBracket_eq_scaled_sampled
    (n : ℕ) (N M q p : ℝ → ℝ)
    (hN : Periodic1 N) (hM : Periodic1 M) (hq : Periodic1 q) (hp : Periodic1 p) :
    (n : ℝ) * continuumLatticeBracket n N M q p
      = (n : ℝ) * sampledDynamicBracketSum n N M q p := by
  rw [continuumLatticeBracket_eq_periodic,
    periodicSampled_eq_sampled_of_periodic n N M q p hN hM hq hp]

/-! ## Ledger terminal -/

/-- THEOREM (ledger terminal, repaired). For 1-periodic ContDiff-1 lapses /
configuration and 1-periodic continuous momentum, the scaled general-`n`
dynamic Hamiltonian bracket at continuum samples tends to the continuum Dirac
density. Proved by Step-3 binding + periodicity +
`dynamic_bracket_shape_continuum_limit`. -/
theorem dirac_algebra_continuum_limit (N M q p : ℝ → ℝ)
    (hNper : Periodic1 N) (hMper : Periodic1 M) (hqper : Periodic1 q)
    (hpper : Periodic1 p)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M) (hq : ContDiff ℝ 1 q)
    (hp : ContinuousOn p (Icc 0 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * continuumLatticeBracket n N M q p)
      atTop
      (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t)) := by
  have hshape :=
    dynamic_bracket_shape_continuum_limit N M q p hN hM hq hp
  refine hshape.congr fun n => ?_
  exact (scaled_continuumLatticeBracket_eq_scaled_sampled
    n N M q p hNper hMper hqper hpper).symm

/-- Unpack: lattice form with explicit `HamDynN` for `n > 0`. -/
theorem dirac_algebra_continuum_limit_hamDynN (N M q p : ℝ → ℝ)
    (hNper : Periodic1 N) (hMper : Periodic1 M) (hqper : Periodic1 q)
    (hpper : Periodic1 p)
    (hN : ContDiff ℝ 1 N) (hM : ContDiff ℝ 1 M) (hq : ContDiff ℝ 1 q)
    (hp : ContinuousOn p (Icc 0 1)) :
    Tendsto
      (fun n : ℕ =>
        if hn : n = 0 then (0 : ℝ)
        else
          haveI : NeZero n := ⟨hn⟩
          (n : ℝ) *
            bracket (HamDynN (sampledLapse n N)) (HamDynN (sampledLapse n M))
              (sampledPhasePoint n q p))
      atTop
      (nhds (∫ t in (0 : ℝ)..1, continuumDiracDensity N M q p t)) := by
  have h := dirac_algebra_continuum_limit N M q p hNper hMper hqper hpper hN hM hq hp
  refine h.congr fun n => ?_
  unfold continuumLatticeBracket
  split_ifs with hn
  · simp [hn]
  · rfl

/-! ### Axiom receipts -/

#print axioms bracket_HamDynN_eq_periodicSampled
#print axioms periodicSampled_eq_sampled_of_periodic
#print axioms dirac_algebra_continuum_limit
#print axioms dirac_algebra_continuum_limit_hamDynN

end
end DiracAlgebraContinuumBinding
end SevenGaps
end Gravity
end IndisputableMonolith
