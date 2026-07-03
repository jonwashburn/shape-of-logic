import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.StandardModel.HiggsEFTBridge
import IndisputableMonolith.StandardModel.HiggsYukawaBridge

/-!
# Higgs Observable Skeleton

This module formalises the *target* surface of Higgs collider observables —
partial widths, branching ratios, and signal-strength modifiers — as
abstract structural objects parametrised by amplitudes and phase-space
factors.

The point of the module is **not** to compute the SM partial widths from
scratch.  It is to expose, in a Lean-checkable form, what it would mean
for the RS theory to "match the SM Higgs phenomenology".  Concretely:

* If the RS-derived Higgs mass equals the SM value,
* If the RS-derived Yukawa coupling for a fermion equals the SM Yukawa,
* If the RS-derived gauge coupling equals the SM gauge coupling,

then the *tree-level* partial width into that channel, computed from the
same amplitude formula in both theories, must be numerically identical.
That is the precise content of "RS reproduces SM observables" at tree
level.

Loop-level corrections (e.g. h → γγ, h → gg) require explicit RS-derived
loop amplitudes; those are *not* yet in Lean and are tagged `LOOP_LEVEL_OPEN`.

## Status

* `THEOREM`: structural identities for total width, branching ratios,
  signal strength.
* `CONDITIONAL_THEOREM`: tree-level matching of an RS partial width to the
  SM partial width when the input couplings agree.
* `OPEN`: loop-level partial widths for `h → γγ`, `h → Zγ`, `h → gg`.
-/

namespace IndisputableMonolith
namespace StandardModel
namespace HiggsObservableSkeleton

open Real
open Constants

noncomputable section

/-! ## §1. Partial Width Schema -/

/-- Abstract schema for a Higgs partial width into a channel.

    `partialWidth amp phaseSpace = phaseSpace * |amp|²`.

    Here `amp` is the (real or modulus) tree amplitude into the channel
    and `phaseSpace` is the kinematic factor (with the `m_H` and final-state
    masses absorbed into it).  Both must be non-negative for a physical
    channel. -/
def partialWidth (amp phaseSpace : ℝ) : ℝ := phaseSpace * amp ^ 2

/-- Partial widths are non-negative for non-negative phase space. -/
theorem partialWidth_nonneg (amp phaseSpace : ℝ) (hps : 0 ≤ phaseSpace) :
    0 ≤ partialWidth amp phaseSpace := by
  unfold partialWidth
  have hamp2 : 0 ≤ amp ^ 2 := sq_nonneg _
  exact mul_nonneg hps hamp2

/-- Two partial widths matched when both amplitudes and phase-space factors
    agree. -/
theorem partialWidth_match
    (amp1 amp2 phaseSpace1 phaseSpace2 : ℝ)
    (hamp : amp1 = amp2) (hps : phaseSpace1 = phaseSpace2) :
    partialWidth amp1 phaseSpace1 = partialWidth amp2 phaseSpace2 := by
  rw [hamp, hps]

/-! ## §2. Total Width and Branching Ratios -/

/-- The total Higgs width is the sum of partial widths over all channels.
    We model "all channels" as a finite list of `(amp, phaseSpace)` pairs. -/
def totalWidth (channels : List (ℝ × ℝ)) : ℝ :=
  (channels.map (fun p => partialWidth p.fst p.snd)).sum

/-- The total width is non-negative when each channel's phase space is. -/
theorem totalWidth_nonneg (channels : List (ℝ × ℝ))
    (hps : ∀ p ∈ channels, 0 ≤ p.snd) :
    0 ≤ totalWidth channels := by
  unfold totalWidth
  induction channels with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead_mem : head ∈ head :: tail := by simp
      have hhead : 0 ≤ partialWidth head.fst head.snd :=
        partialWidth_nonneg head.fst head.snd (hps head hhead_mem)
      have htail : 0 ≤ (tail.map (fun p => partialWidth p.fst p.snd)).sum := by
        apply ih
        intro p hp
        exact hps p (by simp [hp])
      linarith

/-- The branching ratio of a single channel is its partial width over the
    total width.  Defined to be zero if the total width is zero (a
    degenerate, unphysical case). -/
def branchingRatio (amp phaseSpace : ℝ) (channels : List (ℝ × ℝ)) : ℝ :=
  if totalWidth channels = 0 then 0
  else partialWidth amp phaseSpace / totalWidth channels

/-- Branching ratios are non-negative when phase spaces are. -/
theorem branchingRatio_nonneg
    (amp phaseSpace : ℝ) (channels : List (ℝ × ℝ))
    (hps_amp : 0 ≤ phaseSpace)
    (hps : ∀ p ∈ channels, 0 ≤ p.snd) :
    0 ≤ branchingRatio amp phaseSpace channels := by
  unfold branchingRatio
  by_cases h : totalWidth channels = 0
  · simp [h]
  · simp [h]
    have hpw : 0 ≤ partialWidth amp phaseSpace := partialWidth_nonneg amp phaseSpace hps_amp
    have htot : 0 ≤ totalWidth channels := totalWidth_nonneg channels hps
    exact div_nonneg hpw htot

/-! ## §3. Signal-Strength Modifier -/

/-- The signal strength `μ_i = (σ · BR)_RS / (σ · BR)_SM` for a channel.

    By construction, `μ = 1` when both the cross-section and the branching
    ratio match the SM. -/
def signalStrength (sigma_BR_RS sigma_BR_SM : ℝ) : ℝ :=
  if sigma_BR_SM = 0 then 0 else sigma_BR_RS / sigma_BR_SM

/-- The signal-strength modifier equals 1 when both numerator and
    denominator agree. -/
theorem signalStrength_one_of_match
    (x : ℝ) (hx : x ≠ 0) :
    signalStrength x x = 1 := by
  unfold signalStrength
  simp [hx]

/-- Signal strength of zero RS rate is zero. -/
theorem signalStrength_zero_of_RS_zero
    (y : ℝ) (hy : y ≠ 0) :
    signalStrength 0 y = 0 := by
  unfold signalStrength
  simp [hy]

/-! ## §4. Tree-Level Matching Theorem -/

/-- The decisive structural matching theorem: if the RS amplitude and
    phase space for a channel equal their SM counterparts, then the RS
    partial width equals the SM partial width.

    The hypothesis is exactly the content of "RS reproduces the SM tree
    amplitude in this channel."  In practice this hypothesis is satisfied
    once the canonical-normalisation map of `HiggsEFTBridge` and the
    Yukawa map of `HiggsYukawaBridge` are closed for the channel of
    interest. -/
theorem tree_level_partial_width_match
    (amp_RS amp_SM phaseSpace_RS phaseSpace_SM : ℝ)
    (hamp : amp_RS = amp_SM)
    (hps : phaseSpace_RS = phaseSpace_SM) :
    partialWidth amp_RS phaseSpace_RS = partialWidth amp_SM phaseSpace_SM :=
  partialWidth_match amp_RS amp_SM phaseSpace_RS phaseSpace_SM hamp hps

/-- If every channel's RS amplitude and phase space match the SM
    counterparts, then the total widths are equal channel by channel and
    therefore equal in sum. -/
theorem tree_level_total_width_match
    (rsChannels smChannels : List (ℝ × ℝ))
    (h : rsChannels = smChannels) :
    totalWidth rsChannels = totalWidth smChannels := by
  rw [h]

/-- Branching ratios match channel-wise when the underlying channel
    structures match. -/
theorem tree_level_branching_ratio_match
    (amp1 phaseSpace1 amp2 phaseSpace2 : ℝ)
    (rsChannels smChannels : List (ℝ × ℝ))
    (hamp : amp1 = amp2) (hps : phaseSpace1 = phaseSpace2)
    (hch : rsChannels = smChannels) :
    branchingRatio amp1 phaseSpace1 rsChannels
      = branchingRatio amp2 phaseSpace2 smChannels := by
  rw [hamp, hps, hch]

/-! ## §5. Master Skeleton Certificate -/

/-- Master certificate for the Higgs observable skeleton.

    Tags:
    - `THEOREM`: structural identities for partial widths, total widths,
      branching ratios, and signal strengths.
    - `TREE_LEVEL_CONDITIONAL`: the matching theorems are conditional on
      the underlying amplitude/phase-space agreement between RS and SM.
    - `LOOP_LEVEL_OPEN`: loop-induced channels (`h → γγ`, `h → Zγ`,
      `h → gg`) are not formalised here. -/
structure HiggsObservableSkeletonCert where
  /-- THEOREM: partial widths are non-negative on physical phase space. -/
  pw_nonneg     : ∀ amp ps, 0 ≤ ps → 0 ≤ partialWidth amp ps
  /-- THEOREM: total widths are non-negative. -/
  tw_nonneg     : ∀ channels, (∀ p ∈ channels, 0 ≤ p.snd) →
                   0 ≤ totalWidth channels
  /-- THEOREM: branching ratios are non-negative. -/
  br_nonneg     : ∀ amp ps channels, 0 ≤ ps →
                   (∀ p ∈ channels, 0 ≤ p.snd) →
                   0 ≤ branchingRatio amp ps channels
  /-- THEOREM: signal strength equals one when RS and SM rates match. -/
  signal_unity  : ∀ x : ℝ, x ≠ 0 → signalStrength x x = 1
  /-- TREE_LEVEL_CONDITIONAL: partial-width match from amplitude and
      phase-space match. -/
  tree_pw_match : ∀ a1 a2 p1 p2 : ℝ, a1 = a2 → p1 = p2 →
                   partialWidth a1 p1 = partialWidth a2 p2
  /-- TREE_LEVEL_CONDITIONAL: branching-ratio match from channel-wise match. -/
  tree_br_match : ∀ a1 p1 a2 p2 c_rs c_sm,
                   a1 = a2 → p1 = p2 → c_rs = c_sm →
                   branchingRatio a1 p1 c_rs = branchingRatio a2 p2 c_sm

def higgsObservableSkeletonCert : HiggsObservableSkeletonCert where
  pw_nonneg     := partialWidth_nonneg
  tw_nonneg     := totalWidth_nonneg
  br_nonneg     := branchingRatio_nonneg
  signal_unity  := signalStrength_one_of_match
  tree_pw_match := partialWidth_match
  tree_br_match := tree_level_branching_ratio_match

theorem higgsObservableSkeletonCert_inhabited : Nonempty HiggsObservableSkeletonCert :=
  ⟨higgsObservableSkeletonCert⟩

end

end HiggsObservableSkeleton
end StandardModel
end IndisputableMonolith
