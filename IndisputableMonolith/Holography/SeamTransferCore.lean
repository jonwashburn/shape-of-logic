import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Holography.TurnRatioCarrier

/-!
# SeamTransferCore: the balanced pair-fiber transfer forces J (LEG-B Phase B)

**Panel decision 2026-07-05** (`state/panel/censuspricing_20260705_20260705_125417.json`,
judge: Fable over 6 directors; the Scale-Holonomy Trace Core, Phase B): the per-closure
recognition cost of a seam crossing at mismatch ratio `x` is the CHARACTER ANOMALY
`C = Tr(W)/2 − 1` of the transfer `W` that one closure induces on the seam's
double-entry pair fiber. This module lands the per-closure half of that program:

1. **Balance forces the reciprocal leg (THEOREM, the circularity fence).** The panel's
   standing guardrail: never POSIT `W = diag(x, x⁻¹)` (that is J in a trench coat).
   Here the delivered leg scaling by `x` is the only scaling assumed; the conjugate
   `x⁻¹` is DERIVED: a balanced (`det W = 1`) transfer with real eigenvalue `x ≠ 0`
   necessarily has `x⁻¹` as its other eigenvalue (`balanced_conjugate`), because the
   product of the eigenvalues IS the determinant, and double-entry balance pins the
   determinant to 1. Reciprocity is not a modeling choice: it is conservation.

2. **The trace is then forced (THEOREM).** `Tr W = x + x⁻¹` (`balanced_trace`), by
   Cayley–Hamilton on the 2×2 characteristic polynomial `λ² − Tr·λ + det`. Hence the
   character anomaly equals the T5 cost: `Tr(W)/2 − 1 = J(x)` (`charAnomaly_eq_J`).
   J appears NOWHERE in the inputs (a determinant condition and one eigenvalue); it
   emerges from the algebra.

3. **The reduction theorem (THEOREM).** `censusPricing_of_seamTransfer`: if for every
   `(κ, T)` the physical per-cycle cost is the character anomaly of SOME balanced
   transfer whose delivered leg scales by the turn ratio `x = κT/(2π)`, then
   `CensusPricing` holds. The pricing premise of `TurnRatioCarrier` (which names J)
   is thereby REDUCED to `SeamTransferPricing` (which does not): a 2d pair fiber, a
   unit determinant, a delivered-leg eigenvalue, a trace reading. Each conjunct is a
   checkable structural fact about the seam; none names the answer.

4. **The elliptic retrodiction (THEOREM).** The kernel's landed phase-branch poison is
   this frame's elliptic class, on the nose: the character anomaly of the rotation
   transfer IS `phaseCost` (`charAnomaly_rotation`), and a rotation admits NO real
   eigenvalue besides ±1 (`elliptic_no_real_mismatch`) — the elliptic class cannot
   carry a genuine mismatch ratio `x > 0, x ≠ 1` at all. The earlier dead end was not
   bad luck; it was the wrong conjugacy class, provably.

5. **The falsifier, made numeric (THEOREM, panel Live Bet 2).** The two landed census
   observables of the n-fold retrace (absolute surplus `n − 1` posts per sector,
   relative surplus `(n−1)/n` per post) PAIR to exactly `J(n)`
   (`surplus_pairing_eq_J`, via the double-entry pairing identity
   `Jcost_pairing : J(x) = (x−1)(1−x⁻¹)/2`). The pairing pricing and single-column
   (linear) pricing are DISTINGUISHED at the triple cover: `J(3)/J(2) = 8/3 ≠ 2`
   (`cover_cost_ratio_eq`, `pricing_discriminated`); the kernel `decide` facts for the
   triple retrace (closure, census completeness, exactly-3 posts per sector) are
   landed as `witnessWalk3_census`. If the physical seam ever prices the triple cover
   at ratio 2, the trace carrier is dead; 8/3 is its signature.

## Honest scope (do not overclaim)

What is proved here is per-closure matrix algebra plus the reduction: `CensusPricing`
now follows from `SeamTransferPricing`. What is NOT proved is that the physical seam
DELIVERS such a transfer (that the pair fiber is 2-dimensional over ℝ, that one
closure acts on it linearly with the delivered leg scaling by the turn ratio, and that
double-entry balance is unimodularity). That residue is typed here as
`SeamTransferPricing` and stays MODEL until derived from the seam ledger (T2
double-entry + the `PairedCycleFlow` carrier of `SeamCycleCarrier.lean`). The flow
half (Fricke ⇒ d'Alembert ⇒ T5 classification) is Phase A, in a sibling module.
Consumers remain FORCED-CONDITIONAL; the weakest link sets the tag (`soul.mdc`).
-/

namespace IndisputableMonolith
namespace Holography
namespace SeamTransferCore

open Matrix

/-! ## The pair-fiber transfer: eigenvalue and balance -/

/-- `W` has real eigenvalue `x`: some nonzero fiber vector scales by `x` under one
closure. For the seam this is the DELIVERED leg: "the crossing delivers `x` per unit
required" is a scaling statement, definitional for mismatch ratio `x`. Nothing about
the other leg is assumed. -/
def HasRealEigen (W : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ) : Prop :=
  ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ W.mulVec v = x • v

/-- The character anomaly of a transfer: `Tr(W)/2 − 1`. The unique conjugation-
invariant scalar of the closure holonomy, normalized to vanish at the identity. -/
noncomputable def charAnomaly (W : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  W.trace / 2 - 1

/-- **Cayley–Hamilton, evaluated:** the characteristic determinant of a 2×2 transfer
is `y² − Tr·y + det`. -/
lemma det_sub_smul_one (W : Matrix (Fin 2) (Fin 2) ℝ) (y : ℝ) :
    (W - y • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      = y ^ 2 - W.trace * y + W.det := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  norm_num
  ring

/-- A real eigenvalue is a root of the characteristic polynomial:
`x² − Tr·x + det = 0`. -/
lemma eigen_char {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ} (h : HasRealEigen W x) :
    x ^ 2 - W.trace * x + W.det = 0 := by
  obtain ⟨v, hv, hWv⟩ := h
  have hker : (W - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hWv, sub_self]
  have hdet : (W - x • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hker⟩
  rw [det_sub_smul_one] at hdet
  exact hdet

/-- **Balance forces the trace (THEOREM).** A balanced (`det = 1`, double-entry
conservation) transfer whose delivered leg scales by `x ≠ 0` has trace exactly
`x + x⁻¹`. The reciprocal appears in the OUTPUT, derived; it was not an input. -/
theorem balanced_trace {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hdet : W.det = 1) (hx : x ≠ 0) (h : HasRealEigen W x) :
    W.trace = x + x⁻¹ := by
  have hchar := eigen_char h
  rw [hdet] at hchar
  field_simp
  nlinarith [hchar]

/-- **Balance forces the reciprocal leg (THEOREM, the circularity fence honored).**
If a balanced transfer has real eigenvalue `x ≠ 0`, then `x⁻¹` is ALSO an eigenvalue:
the conjugate column scales by the reciprocal because the eigenvalue product IS the
determinant and double-entry pins the determinant to 1. This is the panel's guardrail
discharged: `diag(x, x⁻¹)` is never posited; the `x⁻¹` is a consequence of balance. -/
theorem balanced_conjugate {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hdet : W.det = 1) (hx : x ≠ 0) (h : HasRealEigen W x) :
    HasRealEigen W x⁻¹ := by
  have htr := balanced_trace hdet hx h
  have hdet0 : (W - x⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
    rw [det_sub_smul_one, hdet, htr]
    field_simp
    ring
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  refine ⟨v, hv, ?_⟩
  have := hker
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero] at this
  exact this

/-- **The character anomaly of a balanced transfer IS the T5 cost (THEOREM).**
`Tr(W)/2 − 1 = J(x)` for the delivered ratio `x > 0`. J is never mentioned in the
hypotheses; it emerges from Cayley–Hamilton + balance. -/
theorem charAnomaly_eq_J {W : Matrix (Fin 2) (Fin 2) ℝ} {x : ℝ}
    (hdet : W.det = 1) (hx : 0 < x) (h : HasRealEigen W x) :
    charAnomaly W = Cost.Jcost x := by
  unfold charAnomaly Cost.Jcost
  rw [balanced_trace hdet (ne_of_gt hx) h]

/-! ## Non-vacuity and the balance-reciprocity reading -/

/-- Non-vacuity WITNESS ONLY (this is not the construction, per the circularity
fence): the hyperbolic transfer `diag(x, x⁻¹)` is balanced and delivers `x`. It
shows the structure is inhabited for every ratio; the physical claim is that the
SEAM's transfer inhabits it, which stays the named premise below. -/
noncomputable def hyperbolicWitness (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x, 0; 0, x⁻¹]

theorem hyperbolicWitness_det (x : ℝ) (hx : x ≠ 0) :
    (hyperbolicWitness x).det = 1 := by
  unfold hyperbolicWitness
  rw [Matrix.det_fin_two_of]
  simp [mul_inv_cancel₀ hx]

theorem hyperbolicWitness_eigen (x : ℝ) :
    HasRealEigen (hyperbolicWitness x) x := by
  refine ⟨![1, 0], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · funext i
    fin_cases i <;>
      simp [hyperbolicWitness, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Balance = double-entry reciprocity, read on diagonal transfers:** the credit
leg is the reciprocal of the debit leg EXACTLY when the transfer is balanced. This
is what `det = 1` means on the ledger: the two columns of one posting multiply to
the identity. -/
theorem diag_balanced_iff (a b : ℝ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 ↔ a * b = 1 := by
  rw [Matrix.det_fin_two_of]
  constructor <;> intro h <;> linarith

/-! ## The elliptic retrodiction: the phase branch was the wrong conjugacy class -/

/-- The rotation transfer (the elliptic class): the closure holonomy of the TIME
direction, which closes, as opposed to the mismatch direction, which stretches. -/
noncomputable def rotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem rotation_det (θ : ℝ) : (rotation θ).det = 1 := by
  unfold rotation
  rw [Matrix.det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- **The kernel's phase-branch poison IS the elliptic character (THEOREM).** The
character anomaly of the rotation transfer equals `phaseCost` — the exact object
`TurnRatioCarrier` proved sign-dead (`phaseCost_nonpos`) and lattice-blind
(`phaseCost_vanishes_on_covers`). The earlier dead end is retrodicted: it computed
the right invariant of the WRONG conjugacy class. -/
theorem charAnomaly_rotation (θ : ℝ) :
    charAnomaly (rotation θ) = TurnRatioCarrier.phaseCost θ := by
  unfold charAnomaly rotation
  rw [Matrix.trace_fin_two_of, TurnRatioCarrier.phaseCost_eq]
  ring

/-- **The elliptic class cannot carry a mismatch (THEOREM).** A rotation admits no
real eigenvalue besides ±1: `(x − cos θ)² = cos²θ − 1 ≤ 0` forces `x = cos θ = ±1`.
So no genuine ratio `x > 0, x ≠ 1` lives on the elliptic branch; pricing mismatches
there was structurally impossible, not merely unlucky. -/
theorem elliptic_no_real_mismatch {θ x : ℝ}
    (h : HasRealEigen (rotation θ) x) : x = 1 ∨ x = -1 := by
  have hchar := eigen_char h
  rw [rotation_det] at hchar
  have htr : (rotation θ).trace = 2 * Real.cos θ := by
    unfold rotation
    rw [Matrix.trace_fin_two_of]
    ring
  rw [htr] at hchar
  have hsq : (x - Real.cos θ) ^ 2 = Real.cos θ ^ 2 - 1 := by nlinarith
  have hcos1 : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have hz1 : (x - Real.cos θ) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - Real.cos θ)]
  have hz2 : Real.cos θ ^ 2 = 1 := by nlinarith [sq_nonneg (x - Real.cos θ)]
  have hxcos : x = Real.cos θ := by nlinarith [hz1]
  have hfac : (Real.cos θ - 1) * (Real.cos θ + 1) = 0 := by nlinarith [hz2]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; rw [hxcos]; linarith
  · right; rw [hxcos]; linarith

/-! ## Balance discharged: pairing preservation IS unimodularity (Sp(2,ℝ) = SL(2,ℝ)) -/

/-- The double-entry pairing form on the 2-dimensional pair fiber: the signed area
of the (debit, credit) parallelogram. This is the ledger's conservation object: a
posting and its counter-posting span an oriented area, and double-entry says one
closure cannot create or destroy it. -/
def pairForm (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0

/-- A linear transfer scales the pairing form by exactly its determinant (the 2d
symplectic identity). -/
lemma pairForm_map (W : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) :
    pairForm (W.mulVec u) (W.mulVec v) = W.det * pairForm u v := by
  unfold pairForm
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

/-- **Sp(2, ℝ) = SL(2, ℝ): the balance premise discharged (THEOREM).** A transfer
on the pair fiber preserves the double-entry pairing form IF AND ONLY IF it is
unimodular. `det = 1` is therefore not a structural assumption about the seam: it
is double-entry conservation restated. The panel's "why SL(2)?" question is closed
by this equivalence: a pairing-preserving flow on a 2d real fiber has nowhere else
to live. -/
theorem preserves_pairForm_iff_det_one (W : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ↔ W.det = 1 := by
  constructor
  · intro h
    have h01 := h ![1, 0] ![0, 1]
    rw [pairForm_map] at h01
    have hbase : pairForm ![1, 0] ![0, 1] = 1 := by
      unfold pairForm; simp
    rw [hbase, mul_one] at h01
    exact h01
  · intro h u v
    rw [pairForm_map, h, one_mul]

/-- **Reciprocity is orientation-blindness (THEOREM).** For a balanced transfer,
the trace of the inverse equals the trace: the unoriented invariant of one closure
cannot distinguish over-posting by `x` from under-posting by `x⁻¹`. This is the T5
reciprocal-symmetry hypothesis supplied by the ledger's column-swap symmetry, as a
matrix identity. -/
theorem trace_inv_eq_of_det_one {W V : Matrix (Fin 2) (Fin 2) ℝ}
    (hdet : W.det = 1) (hWV : W * V = 1) : V.trace = W.trace := by
  have hadj : W * W.adjugate = 1 := by
    rw [Matrix.mul_adjugate, hdet, one_smul]
  have hVW : V * W = 1 := Matrix.mul_eq_one_comm.mp hWV
  have hV : V = W.adjugate := by
    calc V = V * (W * W.adjugate) := by rw [hadj, mul_one]
      _ = (V * W) * W.adjugate := by rw [mul_assoc]
      _ = W.adjugate := by rw [hVW, one_mul]
  rw [hV, Matrix.adjugate_fin_two, Matrix.trace_fin_two_of, Matrix.trace_fin_two]
  ring

/-! ## The reduction: CensusPricing from the structural transfer premise -/

/-- **The typed structural premise replacing `CensusPricing` (MODEL until derived).**
For each `(κ, T)` the seam delivers a BALANCED transfer on its 2-dimensional
double-entry pair fiber whose delivered leg scales by the turn ratio, and the
physical per-cycle cost is that transfer's character anomaly. Four checkable
structural facts — 2d fiber, unit determinant (= double-entry conservation),
delivered-leg eigenvalue (= what "mismatch ratio" means), trace reading (= the
unique conjugation-invariant scalar) — and NONE of them names J. -/
def SeamTransferPricing (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ kappa T : ℝ, 0 < kappa → 0 < T →
    ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
      W.det = 1 ∧
      HasRealEigen W (TurnRatioCarrier.turnRatio kappa T) ∧
      C kappa T = charAnomaly W

/-- **The reduction theorem (THEOREM).** Any cost functional priced by a balanced
seam transfer satisfies `CensusPricing`: the pricing premise that named J is now
DOWNSTREAM of a premise that does not. Composing with
`TurnRatioCarrier.b2_unique_zero_of_censusPricing`, the deficit-free period
`β = 2π/κ` is the unique zero of any such functional. -/
theorem censusPricing_of_seamTransfer (C : ℝ → ℝ → ℝ)
    (h : SeamTransferPricing C) : TurnRatioCarrier.CensusPricing C := by
  intro kappa T hk hT
  obtain ⟨W, hdet, heig, hC⟩ := h kappa T hk hT
  rw [hC]
  exact charAnomaly_eq_J hdet (TurnRatioCarrier.turnRatio_pos hk hT) heig

/-- Non-vacuity of the premise: the turn-ratio cost itself is transfer-priced (by
the hyperbolic witness). Existence check only; the physical identification of the
SEAM's transfer stays open. -/
theorem seamTransferPricing_turnRatioCost :
    SeamTransferPricing TurnRatioCarrier.turnRatioCost := by
  intro kappa T hk hT
  have hx : 0 < TurnRatioCarrier.turnRatio kappa T :=
    TurnRatioCarrier.turnRatio_pos hk hT
  refine ⟨hyperbolicWitness (TurnRatioCarrier.turnRatio kappa T),
    hyperbolicWitness_det _ (ne_of_gt hx), hyperbolicWitness_eigen _, ?_⟩
  rw [charAnomaly_eq_J (hyperbolicWitness_det _ (ne_of_gt hx)) hx
    (hyperbolicWitness_eigen _)]
  rfl

/-- **B2 through the reduction (THEOREM):** for any transfer-priced cost functional,
the deficit-free period is the unique zero. The full composition, stated once. -/
theorem b2_unique_zero_of_seamTransfer (C : ℝ → ℝ → ℝ)
    (h : SeamTransferPricing C) (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa :=
  TurnRatioCarrier.b2_unique_zero_of_censusPricing C
    (censusPricing_of_seamTransfer C h) kappa T hk hT

/-! ## The premise in pure ledger language: conservation, not determinant -/

/-- **The premise with the determinant translated away (MODEL until derived).** The
seam's per-cycle transfer CONSERVES the double-entry pairing form (the ledger
conservation statement, no matrix invariant named), some fiber leg scales by the
turn ratio (what "delivered/required mismatch `x`" means), and the physical cost is
the transfer's character anomaly. Via `preserves_pairForm_iff_det_one` this implies
`SeamTransferPricing`, hence `CensusPricing`, hence B2. Every conjunct is now a
LEDGER sentence: conservation, delivery, invariant reading. -/
def ConservingSeamPricing (C : ℝ → ℝ → ℝ) : Prop :=
  ∀ kappa T : ℝ, 0 < kappa → 0 < T →
    ∃ W : Matrix (Fin 2) (Fin 2) ℝ,
      (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ∧
      HasRealEigen W (TurnRatioCarrier.turnRatio kappa T) ∧
      C kappa T = charAnomaly W

/-- Conservation pricing is transfer pricing (`Sp(2) = SL(2)` applied). -/
theorem seamTransferPricing_of_conserving (C : ℝ → ℝ → ℝ)
    (h : ConservingSeamPricing C) : SeamTransferPricing C := by
  intro kappa T hk hT
  obtain ⟨W, hcons, heig, hC⟩ := h kappa T hk hT
  exact ⟨W, (preserves_pairForm_iff_det_one W).mp hcons, heig, hC⟩

/-- **The full Phase-B chain, stated once (THEOREM):** a pairing-CONSERVING seam
transfer delivering the turn ratio prices the census by J, and the deficit-free
period `β = 2π/κ` is its unique zero. From ledger conservation to the B2 discharge
with no J, no cosh, no determinant, and no diagonal form anywhere in the premise. -/
theorem b2_unique_zero_of_conserving (C : ℝ → ℝ → ℝ)
    (h : ConservingSeamPricing C) (kappa T : ℝ) (hk : 0 < kappa) (hT : 0 < T) :
    C kappa T = 0 ↔ T = DeficitFreePeriod.euclideanPeriod kappa :=
  b2_unique_zero_of_seamTransfer C (seamTransferPricing_of_conserving C h) kappa T hk hT

/-! ## The falsifier, made numeric (panel Live Bet 2): 8/3 confirms J, 2 kills it -/

/-- **The double-entry pairing identity (THEOREM).** `J(x) = (x−1)(1−x⁻¹)/2`: the T5
cost is EXACTLY the pairing of the two one-sided relative imbalances of a mismatch
(debit-side surplus `x − 1` against credit-side surplus `1 − x⁻¹`), halved for
once-per-event posting. This is the ledger reading of J: not an exotic functional,
the product of the two column discrepancies any double-entry audit already records. -/
theorem Jcost_pairing (x : ℝ) (hx : x ≠ 0) :
    Cost.Jcost x = (x - 1) * (1 - x⁻¹) / 2 := by
  unfold Cost.Jcost
  field_simp
  ring

/-- The two landed census observables of the n-fold retrace pair to exactly `J(n)`:
absolute surplus `n − 1` (posts per sector beyond the census requirement) times
relative surplus `(n−1)/n` (excess per delivered post), halved. -/
theorem surplus_pairing_eq_J (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 1) * (((n : ℝ) - 1) / n) / 2 = Cost.Jcost n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Jcost_pairing _ hn0]
  field_simp

/-- `J(2) = 1/4` (the double cover). -/
theorem Jcost_two : Cost.Jcost 2 = 1 / 4 := by
  unfold Cost.Jcost
  norm_num

/-- `J(3) = 2/3` (the triple cover). -/
theorem Jcost_three : Cost.Jcost 3 = 2 / 3 := by
  unfold Cost.Jcost
  norm_num

/-- **The trace-carrier signature: `J(3)/J(2) = 8/3` (THEOREM).** -/
theorem cover_cost_ratio_eq : Cost.Jcost 3 / Cost.Jcost 2 = 8 / 3 := by
  rw [Jcost_two, Jcost_three]
  norm_num

/-- **The falsifier record (THEOREM): pairing pricing and linear pricing are
distinguished at the triple cover.** Linear (single-column surplus) pricing gives
cost ratio `(3−1)/(2−1) = 2`; the double-entry pairing gives `8/3`. A measured or
derived seam pricing of the triple retrace at ratio 2 KILLS the trace carrier; 8/3
is its confirmation. The two hypotheses are not observationally equivalent. -/
theorem pricing_discriminated :
    Cost.Jcost 3 / Cost.Jcost 2 ≠ (((3 : ℝ) - 1) / ((2 : ℝ) - 1)) := by
  rw [cover_cost_ratio_eq]
  norm_num

open TurnRatioCarrier EightTickSubperiodExclusion in
/-- **The triple retrace census record (THEOREM, kernel `decide`).** The 3-fold
retrace of the witness 8-walk (a closed 24-walk) is census-complete and posts each
admissible sector EXACTLY 3 times: absolute surplus 2 per sector, relative surplus
2/3 per post — the two factors whose pairing is `J(3) = 2/3`
(`surplus_pairing_eq_J`). Extends the n = 2 record of
`TurnRatioCarrier.eight_tick_multiple_exclusion` to the cover that discriminates
the pricing laws. -/
theorem witnessWalk3_census :
    walkEnd 0 (witnessWalk ++ witnessWalk ++ witnessWalk) = 0 ∧
    censusComplete 0 (witnessWalk ++ witnessWalk ++ witnessWalk) = true ∧
    visitCount 0 (witnessWalk ++ witnessWalk ++ witnessWalk) [0] = 3 ∧
    visitCount 0 (witnessWalk ++ witnessWalk ++ witnessWalk) [3, 6, 12, 9] = 3 ∧
    visitCount 0 (witnessWalk ++ witnessWalk ++ witnessWalk) [5, 10] = 3 ∧
    visitCount 0 (witnessWalk ++ witnessWalk ++ witnessWalk) [15] = 3 := by
  decide

/-! ## Certificate -/

/-- Bundled certificate for the Phase-B per-closure core: balance forces the
reciprocal leg and the trace, the character anomaly is J, the reduction to
`CensusPricing` holds, the elliptic branch is retrodicted and mismatch-dead, and
the pricing falsifier is discriminating. All fields unconditional THEOREMs; the
structural premise (`SeamTransferPricing` for the PHYSICAL seam) is consumed only
by the reduction theorem, stated separately. -/
structure SeamTransferCoreCert : Prop where
  conjugate_forced : ∀ (W : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ),
    W.det = 1 → x ≠ 0 → HasRealEigen W x → HasRealEigen W x⁻¹
  anomaly_is_J : ∀ (W : Matrix (Fin 2) (Fin 2) ℝ) (x : ℝ),
    W.det = 1 → 0 < x → HasRealEigen W x → charAnomaly W = Cost.Jcost x
  reduction : ∀ C : ℝ → ℝ → ℝ,
    SeamTransferPricing C → TurnRatioCarrier.CensusPricing C
  elliptic_is_phaseCost : ∀ θ : ℝ,
    charAnomaly (rotation θ) = TurnRatioCarrier.phaseCost θ
  elliptic_mismatch_dead : ∀ θ x : ℝ,
    HasRealEigen (rotation θ) x → x = 1 ∨ x = -1
  pairing_identity : ∀ x : ℝ, x ≠ 0 → Cost.Jcost x = (x - 1) * (1 - x⁻¹) / 2
  falsifier_discriminates :
    Cost.Jcost 3 / Cost.Jcost 2 ≠ (((3 : ℝ) - 1) / ((2 : ℝ) - 1))
  balance_is_conservation : ∀ W : Matrix (Fin 2) (Fin 2) ℝ,
    (∀ u v, pairForm (W.mulVec u) (W.mulVec v) = pairForm u v) ↔ W.det = 1
  reciprocity_forced : ∀ W V : Matrix (Fin 2) (Fin 2) ℝ,
    W.det = 1 → W * V = 1 → V.trace = W.trace

/-- The certificate holds. -/
theorem seamTransferCoreCert : SeamTransferCoreCert where
  conjugate_forced := fun _ _ hdet hx h => balanced_conjugate hdet hx h
  anomaly_is_J := fun _ _ hdet hx h => charAnomaly_eq_J hdet hx h
  reduction := censusPricing_of_seamTransfer
  elliptic_is_phaseCost := charAnomaly_rotation
  elliptic_mismatch_dead := fun _ _ h => elliptic_no_real_mismatch h
  pairing_identity := Jcost_pairing
  falsifier_discriminates := pricing_discriminated
  balance_is_conservation := preserves_pairForm_iff_det_one
  reciprocity_forced := fun _ _ hdet hWV => trace_inv_eq_of_det_one hdet hWV

end SeamTransferCore
end Holography
end IndisputableMonolith
