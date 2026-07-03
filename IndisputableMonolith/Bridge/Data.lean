import Mathlib
import IndisputableMonolith.Core
import IndisputableMonolith.RecogSpec.Scales
import IndisputableMonolith.Bridge.DataCore

/-!
Bridge Data Module

This module contains the BridgeData structure and associated physical constants,
dimensionless identities, and bridge-related functions for the recognition system.
-/

namespace IndisputableMonolith.BridgeData

/-!
Core bridge-anchor data and the λ_rec dimensionless identity live in
`IndisputableMonolith.Bridge.DataCore`.

This file extends the core with additional measurement/protocol helpers.
-/

/-- K_A = φ (golden ratio constant). -/
noncomputable def K_A (_ : BridgeData) : ℝ := IndisputableMonolith.Constants.K

/-- K_B = λ_rec/ℓ0. -/
noncomputable def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

/-- Combined uncertainty aggregator (policy hook; can be specialized by callers). -/
noncomputable def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := Real.sqrt (u_ell0^2 + u_lrec^2)

lemma u_comb_nonneg (B : BridgeData) (u_ell0 u_lrec : ℝ) :
  0 ≤ u_comb B u_ell0 u_lrec := by
  dsimp [u_comb]
  exact Real.sqrt_nonneg _

lemma u_comb_comm (B : BridgeData) (u_ell0 u_lrec : ℝ) :
  u_comb B u_ell0 u_lrec = u_comb B u_lrec u_ell0 := by
  dsimp [u_comb]
  have : u_ell0 ^ 2 + u_lrec ^ 2 = u_lrec ^ 2 + u_ell0 ^ 2 := by
    simpa [add_comm]
  simpa [this]

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
noncomputable def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (abs (KA - KB)) / (k * u)

/-- Boolean pass at threshold k: Z ≤ 1. Publishes the exact Z expression. -/
noncomputable def passAt (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Bool :=
  decide ((Zscore B u_ell0 u_lrec k) ≤ 1)

/-- `passAt` agrees with the underlying inequality test. -/
@[simp] lemma passAt_true_iff (B : BridgeData) (u_ell0 u_lrec k : ℝ) :
  passAt B u_ell0 u_lrec k = true ↔ Zscore B u_ell0 u_lrec k ≤ 1 := by
  dsimp [passAt]
  by_cases h : Zscore B u_ell0 u_lrec k ≤ 1
  · simp [h]
  · simp [h]

/-- Full witness record for publication. -/
structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool

/-- Witness constructor. -/
noncomputable def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

end IndisputableMonolith.BridgeData
