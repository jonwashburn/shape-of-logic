import IndisputableMonolith.Foundation.RecognitionLedgerFloor
import IndisputableMonolith.Foundation.DAlembert.FactorizationForcing

/-!
# Ledger to Factorization Bridge

Phase 3 asks for the T4-to-T5 bridge to be derived from the recognition ledger
rather than assumed as an analytic input.  This file isolates the precise
remaining algebraic condition.

The free ledger already proves unconditional additivity.  If a two-variable
combiner has the corresponding ledger-linear response in its second argument,
then the `rightAffine` field used by the d'Alembert factorization gate follows.
Together with symmetry, the boundary law, and the unit diagonal, the existing
gate theorem forces the RCL polynomial.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerToFactorization

open DAlembert.FactorizationForcing

/-- Monotone additive real responses are linear.  This is the order-regularity
replacement for the continuity gate in the additive Cauchy step. -/
theorem monotone_additive_isLinear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hmono : Monotone f) :
    ∀ x, f x = f 1 * x := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linarith
  let F : ℝ →+ ℝ := AddMonoidHom.mk' f (fun a b => hadd a b)
  have hFcoe : ∀ y, F y = f y := fun _ => rfl
  have hFq : ∀ q : ℚ, f (q : ℝ) = f 1 * (q : ℝ) := by
    intro q
    have h := map_ratCast_smul F ℝ ℝ q (1 : ℝ)
    simp only [smul_eq_mul, mul_one, hFcoe] at h
    rw [h]
    ring
  intro x
  set c := f 1 with hc_def
  have hc : 0 ≤ c := by
    have hmle : f 0 ≤ f 1 := hmono (by norm_num)
    rw [hf0] at hmle
    exact hmle
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · have hub : f x ≤ 0 := by
      obtain ⟨r, hxr, -⟩ := exists_rat_btwn (lt_add_one x)
      have hmr := hmono hxr.le
      rw [hFq r, ← hc0, zero_mul] at hmr
      exact hmr
    have hlb : 0 ≤ f x := by
      obtain ⟨q, -, hqx⟩ := exists_rat_btwn (sub_one_lt x)
      have hmq := hmono hqx.le
      rw [hFq q, ← hc0, zero_mul] at hmq
      exact hmq
    rw [← hc0, zero_mul]
    linarith
  · refine le_antisymm ?_ ?_
    · by_contra hcon
      push_neg at hcon
      have hxlt : x < f x / c := by
        rw [lt_div_iff₀ hcpos]
        linarith [mul_comm c x]
      obtain ⟨r, hxr, hrlt⟩ := exists_rat_btwn hxlt
      have h1 : f x ≤ c * (r : ℝ) := by
        have hm := hmono hxr.le
        rwa [hFq r] at hm
      have h2 : c * (r : ℝ) < f x := by
        have := (lt_div_iff₀ hcpos).mp hrlt
        linarith [mul_comm (r : ℝ) c]
      linarith
    · by_contra hcon
      push_neg at hcon
      have hxlt : f x / c < x := by
        rw [div_lt_iff₀ hcpos]
        linarith [mul_comm c x]
      obtain ⟨q, hqlt, hqx⟩ := exists_rat_btwn hxlt
      have h1 : c * (q : ℝ) ≤ f x := by
        have hm := hmono hqx.le
        rwa [hFq q] at hm
      have h2 : f x < c * (q : ℝ) := by
        have := (div_lt_iff₀ hcpos).mp hqlt
        linarith [mul_comm (q : ℝ) c]
      linarith

/-- Antitone additive real responses are linear.  Apply the monotone lemma to
`-f`.  This is the second branch of the directional (order) regularity route:
the RCL response slope `2(u+1)` is negative for `u < -1`, so the response is
antitone there, not monotone. -/
theorem antitone_additive_isLinear {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y) (hanti : Antitone f) :
    ∀ x, f x = f 1 * x := by
  have hadd' : ∀ x y, (fun t => -f t) (x + y) =
      (fun t => -f t) x + (fun t => -f t) y := by
    intro x y
    simp only [hadd x y]
    ring
  have hmono' : Monotone (fun t => -f t) := by
    intro a b hab
    simp only [neg_le_neg_iff]
    exact hanti hab
  have h := monotone_additive_isLinear hadd' hmono'
  intro x
  have hx : -f x = -f 1 * x := h x
  have hx2 : -f x = -(f 1 * x) := by rw [hx]; ring
  linarith

/-- An additive real response that never decreases cost on non-negatively posted
mass is monotone everywhere.  This is the order shadow of `ledgerCost_nonneg`:
adding defect mass `b - a ≥ 0` adds non-negative cost, so the response is
non-decreasing.  No continuity or completeness is used. -/
theorem additive_nonnegOnNonneg_isMonotone {f : ℝ → ℝ}
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hnn : ∀ x, 0 ≤ x → 0 ≤ f x) : Monotone f := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linarith
  intro a b hab
  have hsub : f b = f (b - a) + f a := by
    have h := hadd (b - a) a
    rw [sub_add_cancel] at h
    exact h
  have hnn' : 0 ≤ f (b - a) := hnn (b - a) (by linarith)
  linarith

/-- Ledger-linear response for a combiner: the second argument is governed by
its response to one unit of posted ledger mass.  The `free_ledger_additivity`
field pins this bridge to the existing free-ledger theorem rather than leaving
it as prose. -/
structure LedgerLinearResponse (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6
  rightResponse :
    ∀ u v, P u v = (P u 1 - P u 0) * v + P u 0
  free_ledger_additivity :
    ∀ (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) =
        RecognitionLedgerFloor.ledgerCost w Γ +
          RecognitionLedgerFloor.ledgerCost w Δ

/-- Free-ledger semantics for a candidate factorization combiner.  The response
law is intentionally weaker than `LedgerLinearResponse`: it records additive
posting in the second coordinate plus a regularity gate, leaving Cauchy
linearization as a theorem rather than a field. -/
structure FreeLedgerCombinerSemantics (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6
  rightPostedAdditive :
    ∀ u v w,
      P u (v + w) - P u 0 =
        (P u v - P u 0) + (P u w - P u 0)
  rightContinuous : ∀ u, Continuous fun v => P u v
  free_ledger_additivity :
    ∀ (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) =
        RecognitionLedgerFloor.ledgerCost w Γ +
          RecognitionLedgerFloor.ledgerCost w Δ

/-- Primitive ledger-posting semantics: the second coordinate is fed directly by
the cost of actual free defect ledgers, and posting ledgers additively is the
operation seen by the combiner.  This is closer to the Phase-2 ledger than the
`DiscreteLedgerPostingSemantics` surface, which only talks about natural-number
costs after choosing the rank-one unit ledger. -/
structure PrimitiveLedgerPostingSemantics (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6
  rightLedgerPostedAdditive :
    ∀ (u : ℝ) (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      P u (RecognitionLedgerFloor.ledgerCost w (Γ + Δ)) - P u 0 =
        (P u (RecognitionLedgerFloor.ledgerCost w Γ) - P u 0) +
          (P u (RecognitionLedgerFloor.ledgerCost w Δ) - P u 0)
  free_ledger_additivity :
    ∀ (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) =
        RecognitionLedgerFloor.ledgerCost w Γ +
          RecognitionLedgerFloor.ledgerCost w Δ

/-- Primitive ledger posting over arbitrary weighted defect ledgers gives the
additive response law for arbitrary real postings. -/
theorem primitiveLedgerPosting_forces_rightPostedAdditive
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P) :
    ∀ u v w,
      P u (v + w) - P u 0 =
        (P u v - P u 0) + (P u w - P u 0) := by
  intro u v w
  let weight : Bool → ℝ := fun b => if b then w else v
  let Γ : RecognitionLedgerFloor.DefectLedger Bool := Finsupp.single false 1
  let Δ : RecognitionLedgerFloor.DefectLedger Bool := Finsupp.single true 1
  have hpost := h.rightLedgerPostedAdditive u Bool weight Γ Δ
  have hΓ : RecognitionLedgerFloor.ledgerCost weight Γ = v := by
    simp [Γ, weight, RecognitionLedgerFloor.ledgerCost_single]
  have hΔ : RecognitionLedgerFloor.ledgerCost weight Δ = w := by
    simp [Δ, weight, RecognitionLedgerFloor.ledgerCost_single]
  have hsum : RecognitionLedgerFloor.ledgerCost weight (Γ + Δ) = v + w := by
    rw [RecognitionLedgerFloor.ledgerCost_add, hΓ, hΔ]
  simpa [hΓ, hΔ, hsum] using hpost

/-- Primitive ledger posting plus continuity gives the completed free-ledger
posting semantics.  The additive response law is no longer a separate
assumption: realize arbitrary real postings `v` and `w` as the costs of two
primitive defects in a two-generator ledger. -/
theorem freeLedgerCombinerSemantics_from_primitiveLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hcont : ∀ u, Continuous fun v => P u v) :
    FreeLedgerCombinerSemantics P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightPostedAdditive := ?_
    rightContinuous := hcont
    free_ledger_additivity := h.free_ledger_additivity
  }
  exact primitiveLedgerPosting_forces_rightPostedAdditive P h

/-- Discrete posting semantics on the actual rank-one ledger-cost surface.
The second coordinate is restricted to natural-number ledger costs, i.e. the
values produced by finite multiplicities before analytic completion. -/
structure DiscreteLedgerPostingSemantics (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6
  rightNatPostedAdditive :
    ∀ (u : ℝ) (m n : ℕ),
      P u ((m + n : ℕ) : ℝ) - P u 0 =
        (P u (m : ℝ) - P u 0) + (P u (n : ℝ) - P u 0)
  free_ledger_additivity :
    ∀ (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) =
        RecognitionLedgerFloor.ledgerCost w Γ +
          RecognitionLedgerFloor.ledgerCost w Δ

/-- Primitive ledger posting specializes to the natural-number rank-one ledger
surface. -/
theorem discreteLedgerPosting_from_primitiveLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P) :
    DiscreteLedgerPostingSemantics P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightNatPostedAdditive := ?_
    free_ledger_additivity := h.free_ledger_additivity
  }
  intro u m n
  let Γ : RecognitionLedgerFloor.DefectLedger Unit := Finsupp.single () m
  let Δ : RecognitionLedgerFloor.DefectLedger Unit := Finsupp.single () n
  have hpost := h.rightLedgerPostedAdditive u Unit (fun _ : Unit => (1 : ℝ)) Γ Δ
  have hΓ :
      RecognitionLedgerFloor.ledgerCost (fun _ : Unit => (1 : ℝ)) Γ = (m : ℝ) := by
    simpa [Γ] using RecognitionLedgerFloor.unit_cost_is_generator_count (I := Unit) () m
  have hΔ :
      RecognitionLedgerFloor.ledgerCost (fun _ : Unit => (1 : ℝ)) Δ = (n : ℝ) := by
    simpa [Δ] using RecognitionLedgerFloor.unit_cost_is_generator_count (I := Unit) () n
  have hsum :
      RecognitionLedgerFloor.ledgerCost (fun _ : Unit => (1 : ℝ)) (Γ + Δ) =
        ((m + n : ℕ) : ℝ) := by
    rw [RecognitionLedgerFloor.ledgerCost_add, hΓ, hΔ]
    norm_num
  simpa [hΓ, hΔ, hsum] using hpost

/-- Rational posting semantics on the countable positive-ratio completion of
the free ledger.  This is the analytic-completion input: rational ledger costs
already follow the affine response law, and the response is continuous in the
completed real coordinate. -/
structure RationalLedgerPostingSemantics (P : ℝ → ℝ → ℝ) : Prop where
  symmetric : ∀ u v, P u v = P v u
  zeroBoundary : ∀ u, P u 0 = 2 * u
  unitDiagonal : P 1 1 = 6
  rightContinuous : ∀ u, Continuous fun v => P u v
  rightRatAffine :
    ∀ (u : ℝ) (q : ℚ),
      P u (q : ℝ) - P u 0 = (q : ℝ) * (P u 1 - P u 0)
  free_ledger_additivity :
    ∀ (I : Type) (w : I → ℝ)
      (Γ Δ : RecognitionLedgerFloor.DefectLedger I),
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) =
        RecognitionLedgerFloor.ledgerCost w Γ +
          RecognitionLedgerFloor.ledgerCost w Δ

/-- Discrete ledger posting forces affine response on the actual
natural-number ledger-cost surface.  This is the finite-ledger version of
right-affineness: no real-continuum completion is used here. -/
theorem discreteLedgerPosting_forces_natAffineResponse
    (P : ℝ → ℝ → ℝ) (h : DiscreteLedgerPostingSemantics P) :
    ∀ u (n : ℕ),
      P u (n : ℝ) = (P u 1 - P u 0) * (n : ℝ) + P u 0 := by
  intro u n
  let R : ℕ → ℝ := fun k => P u (k : ℝ) - P u 0
  have hRadd : ∀ m n : ℕ, R (m + n) = R m + R n := by
    intro m n
    exact h.rightNatPostedAdditive u m n
  have hR : ∀ n : ℕ, R n = (n : ℝ) * R 1 := by
    intro n
    induction n with
    | zero =>
        simp [R]
    | succ n ih =>
        have hstep : R (n + 1) = R n + R 1 := hRadd n 1
        have hsucc : R (Nat.succ n) = R n + R 1 := by
          simpa [Nat.succ_eq_add_one] using hstep
        rw [hsucc, ih]
        norm_num
        ring
  have hRn : P u (n : ℝ) - P u 0 = (n : ℝ) * (P u 1 - P u 0) := by
    simpa [R] using hR n
  have hcomm :
      (n : ℝ) * (P u 1 - P u 0) =
        (P u 1 - P u 0) * (n : ℝ) := by
    ring
  linarith

/-- Primitive ledger posting already forces affine response on the actual
natural-number rank-one ledger-cost surface. -/
theorem primitiveLedgerPosting_forces_natAffineResponse
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P) :
    ∀ u (n : ℕ),
      P u (n : ℝ) = (P u 1 - P u 0) * (n : ℝ) + P u 0 :=
  discreteLedgerPosting_forces_natAffineResponse P
    (discreteLedgerPosting_from_primitiveLedgerPosting P h)

/-- The canonical RCL combiner carries the discrete free-ledger posting
semantics before analytic completion. -/
theorem rclCombiner_discreteLedgerPostingSemantics :
    DiscreteLedgerPostingSemantics rclCombiner where
  symmetric := rclCombiner_satisfies_gate.symmetric
  zeroBoundary := rclCombiner_satisfies_gate.zeroBoundary
  unitDiagonal := rclCombiner_satisfies_gate.unitDiagonal
  rightNatPostedAdditive := by
    intro u m n
    unfold rclCombiner
    norm_num
    ring
  free_ledger_additivity := by
    intro I w Γ Δ
    exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- The canonical RCL combiner satisfies the primitive free-ledger posting law
before passing to the rank-one natural-number surface. -/
theorem rclCombiner_primitiveLedgerPostingSemantics :
    PrimitiveLedgerPostingSemantics rclCombiner where
  symmetric := rclCombiner_satisfies_gate.symmetric
  zeroBoundary := rclCombiner_satisfies_gate.zeroBoundary
  unitDiagonal := rclCombiner_satisfies_gate.unitDiagonal
  rightLedgerPostedAdditive := by
    intro u I w Γ Δ
    rw [RecognitionLedgerFloor.ledgerCost_add]
    unfold rclCombiner
    ring
  free_ledger_additivity := by
    intro I w Γ Δ
    exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- Rational ledger posting plus continuity completes the response from the
dense rational ledger-ratio surface to all real completed costs. -/
theorem ledgerLinearResponse_from_rationalLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : RationalLedgerPostingSemantics P) :
    LedgerLinearResponse P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightResponse := ?_
    free_ledger_additivity := h.free_ledger_additivity
  }
  intro u v
  let f : ℝ → ℝ := fun x => P u x - P u 0
  let g : ℝ → ℝ := fun x => x * (P u 1 - P u 0)
  have hf : Continuous f := by
    exact (h.rightContinuous u).sub continuous_const
  have hg : Continuous g := by
    exact continuous_id.mul continuous_const
  have hdense : DenseRange (fun q : ℚ => (q : ℝ)) :=
    Rat.denseRange_cast
  have hfg : f = g := by
    refine DenseRange.equalizer hdense hf hg ?_
    funext q
    exact h.rightRatAffine u q
  have hv := congrFun hfg v
  change P u v - P u 0 = v * (P u 1 - P u 0) at hv
  have hcomm : v * (P u 1 - P u 0) = (P u 1 - P u 0) * v := by
    ring
  linarith

/-- The canonical RCL combiner satisfies the rational completed posting
semantics. -/
theorem rclCombiner_rationalLedgerPostingSemantics :
    RationalLedgerPostingSemantics rclCombiner where
  symmetric := rclCombiner_satisfies_gate.symmetric
  zeroBoundary := rclCombiner_satisfies_gate.zeroBoundary
  unitDiagonal := rclCombiner_satisfies_gate.unitDiagonal
  rightContinuous := by
    intro u
    unfold rclCombiner
    continuity
  rightRatAffine := by
    intro u q
    unfold rclCombiner
    norm_num
    ring
  free_ledger_additivity := by
    intro I w Γ Δ
    exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- Completed ledger-linear response is exactly rational ledger posting plus
continuity.  The forward direction is algebraic; the reverse direction is the
dense-rational completion theorem above. -/
theorem rationalLedgerPosting_iff_ledgerLinearResponse (P : ℝ → ℝ → ℝ) :
    RationalLedgerPostingSemantics P ↔ LedgerLinearResponse P := by
  constructor
  · exact ledgerLinearResponse_from_rationalLedgerPosting P
  · intro h
    refine {
      symmetric := h.symmetric
      zeroBoundary := h.zeroBoundary
      unitDiagonal := h.unitDiagonal
      rightContinuous := ?_
      rightRatAffine := ?_
      free_ledger_additivity := h.free_ledger_additivity
    }
    · intro u
      have hfun :
          (fun v => P u v) =
            fun v => (P u 1 - P u 0) * v + P u 0 := by
        funext v
        exact h.rightResponse u v
      rw [hfun]
      exact (continuous_const.mul continuous_id).add continuous_const
    · intro u q
      rw [h.rightResponse u (q : ℝ)]
      ring

/-- Continuous additive posting response is linear over `ℝ`, so free-ledger
semantics supplies the exact `LedgerLinearResponse` bridge. -/
theorem ledgerLinearResponse_from_free_ledger
    (P : ℝ → ℝ → ℝ) (h : FreeLedgerCombinerSemantics P) :
    LedgerLinearResponse P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightResponse := ?_
    free_ledger_additivity := h.free_ledger_additivity
  }
  intro u v
  let response : ℝ →+ ℝ := {
    toFun := fun t => P u t - P u 0
    map_zero' := by ring
    map_add' := by
      intro a b
      exact h.rightPostedAdditive u a b
  }
  have hresponse_cont : Continuous response := by
    change Continuous fun t => P u t - P u 0
    exact (h.rightContinuous u).sub continuous_const
  let linearResponse : ℝ →L[ℝ] ℝ :=
    AddMonoidHom.toRealLinearMap response hresponse_cont
  have hlinear :
      response v = v * response 1 := by
    have hsmul := linearResponse.map_smul v 1
    change response (v * 1) = v * response 1 at hsmul
    simpa using hsmul
  change P u v = (P u 1 - P u 0) * v + P u 0
  have hcomm : v * (P u 1 - P u 0) = (P u 1 - P u 0) * v := by ring
  have hsub : P u v - P u 0 = (P u 1 - P u 0) * v := by
    simpa [response, hcomm] using hlinear
  linarith

/-- Primitive ledger posting plus continuity forces completed real
ledger-linear response. -/
theorem ledgerLinearResponse_from_primitiveLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hcont : ∀ u, Continuous fun v => P u v) :
    LedgerLinearResponse P :=
  ledgerLinearResponse_from_free_ledger P
    (freeLedgerCombinerSemantics_from_primitiveLedgerPosting P h hcont)

/-- Primitive ledger posting plus a *globally* monotone response gives completed
real ledger-linear response.  WARNING (honesty): the global-monotone hypothesis
is vacuous for the target combiner: the forced conclusion is RCL, whose response
slope `2(u+1)` is negative for `u < -1`, so no `P` satisfies both this hypothesis
and the conclusion.  The genuine, non-vacuous order route is
`ledgerLinearResponse_from_primitiveLedgerPosting_directional` below (monotone OR
antitone per slice); this monotone-only form is kept as a special case and as a
proof component, and is non-vacuous only on the physical cost cone `u ≥ -1`. -/
theorem ledgerLinearResponse_from_primitiveLedgerPosting_monotone
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hmono : ∀ u, Monotone fun v => P u v) :
    LedgerLinearResponse P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightResponse := ?_
    free_ledger_additivity := h.free_ledger_additivity
  }
  intro u v
  let response : ℝ → ℝ := fun t => P u t - P u 0
  have hadd : ∀ x y, response (x + y) = response x + response y := by
    intro x y
    exact primitiveLedgerPosting_forces_rightPostedAdditive P h u x y
  have hresponse_mono : Monotone response := by
    intro a b hab
    exact sub_le_sub_right ((hmono u) hab) (P u 0)
  have hlin := monotone_additive_isLinear hadd hresponse_mono v
  have hsub : P u v - P u 0 = (P u 1 - P u 0) * v := by
    simpa [response] using hlin
  linarith

/-- Primitive ledger posting plus **global** cost non-negativity gives completed
real ledger-linear response.  WARNING (honesty): like the monotone form above,
the *global* non-negativity hypothesis (`P u 0 ≤ P u v` for all `u`, all `v ≥ 0`)
is vacuous for the target combiner; RCL fails it for `u < -1`.  It holds on the
physical cost cone `u ≥ 0` (`rclCombiner_postingNonneg`), where it is the genuine
order shadow of `ledgerCost_nonneg`.  For the non-vacuous global closure use
`ledgerLinearResponse_from_primitiveLedgerPosting_directional`. -/
theorem ledgerLinearResponse_from_primitiveLedgerPosting_nonneg
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hnn : ∀ u v, 0 ≤ v → P u 0 ≤ P u v) :
    LedgerLinearResponse P := by
  refine ledgerLinearResponse_from_primitiveLedgerPosting_monotone P h ?_
  intro u
  have hadd : ∀ x y,
      (fun v => P u v - P u 0) (x + y) =
        (fun v => P u v - P u 0) x + (fun v => P u v - P u 0) y := by
    intro x y
    exact primitiveLedgerPosting_forces_rightPostedAdditive P h u x y
  have hfnn : ∀ x, 0 ≤ x → 0 ≤ (fun v => P u v - P u 0) x := by
    intro x hx
    have := hnn u x hx
    simp only
    linarith
  have hmono := additive_nonnegOnNonneg_isMonotone hadd hfnn
  intro a b hab
  have hle := hmono hab
  simp only at hle
  linarith

/-- Primitive ledger posting plus **per-slice directional regularity** forces the
completed real ledger-linear response.  For each fixed first cost `u`, the
combined cost responds to posted mass `v` in one consistent order direction
(monotone or antitone).  This is the genuine, non-vacuous order replacement for
the analytic continuity gate: unlike global monotonicity, the canonical RCL
combiner provably satisfies this (its response slope `2(u+1)` has a fixed sign
for each `u`), so the forcing hypothesis is consistent with its conclusion. -/
theorem ledgerLinearResponse_from_primitiveLedgerPosting_directional
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v)) :
    LedgerLinearResponse P := by
  refine {
    symmetric := h.symmetric
    zeroBoundary := h.zeroBoundary
    unitDiagonal := h.unitDiagonal
    rightResponse := ?_
    free_ledger_additivity := h.free_ledger_additivity
  }
  intro u v
  let response : ℝ → ℝ := fun t => P u t - P u 0
  have hadd : ∀ x y, response (x + y) = response x + response y := by
    intro x y
    exact primitiveLedgerPosting_forces_rightPostedAdditive P h u x y
  have hlin : ∀ x, response x = response 1 * x := by
    rcases hdir u with hmono | hanti
    · have hrmono : Monotone response := by
        intro a b hab
        exact sub_le_sub_right (hmono hab) (P u 0)
      exact monotone_additive_isLinear hadd hrmono
    · have hranti : Antitone response := by
        intro a b hab
        exact sub_le_sub_right (hanti hab) (P u 0)
      exact antitone_additive_isLinear hadd hranti
  have hsub : P u v - P u 0 = (P u 1 - P u 0) * v := by
    simpa [response] using hlin v
  linarith

/-- Completed ledger-linear response is exactly free-ledger posting semantics
plus continuity. -/
theorem freeLedgerCombinerSemantics_iff_ledgerLinearResponse (P : ℝ → ℝ → ℝ) :
    FreeLedgerCombinerSemantics P ↔ LedgerLinearResponse P := by
  constructor
  · exact ledgerLinearResponse_from_free_ledger P
  · intro h
    refine {
      symmetric := h.symmetric
      zeroBoundary := h.zeroBoundary
      unitDiagonal := h.unitDiagonal
      rightPostedAdditive := ?_
      rightContinuous := ?_
      free_ledger_additivity := h.free_ledger_additivity
    }
    · intro u v w
      rw [h.rightResponse u (v + w), h.rightResponse u v, h.rightResponse u w]
      ring
    · intro u
      have hfun :
          (fun v => P u v) =
            fun v => (P u 1 - P u 0) * v + P u 0 := by
        funext v
        exact h.rightResponse u v
      rw [hfun]
      exact (continuous_const.mul continuous_id).add continuous_const

/-- Ledger-linear response supplies the `rightAffine` field of the
factorization gate. -/
theorem rightAffine_of_ledgerLinearResponse
    (P : ℝ → ℝ → ℝ) (h : LedgerLinearResponse P) :
    ∀ u, ∃ α β, ∀ v, P u v = α * v + β := by
  intro u
  exact ⟨P u 1 - P u 0, P u 0, h.rightResponse u⟩

/-- Ledger-linear response plus the remaining gate fields gives the full
factorization gate. -/
theorem factorizationGate_of_ledgerLinearResponse
    (P : ℝ → ℝ → ℝ) (h : LedgerLinearResponse P) :
    FactorizationAssociativityGate P where
  symmetric := h.symmetric
  rightAffine := rightAffine_of_ledgerLinearResponse P h
  zeroBoundary := h.zeroBoundary
  unitDiagonal := h.unitDiagonal

/-- Ledger-linear response forces the RCL polynomial through the existing gate
theorem. -/
theorem ledgerLinearResponse_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : LedgerLinearResponse P) :
    ∀ u v, P u v = rclCombiner u v := by
  intro u v
  rw [gate_forces_rcl P (factorizationGate_of_ledgerLinearResponse P h) u v]
  rfl

/-- Primitive ledger posting plus continuity supplies the full factorization
gate. -/
theorem factorizationGate_of_primitiveLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hcont : ∀ u, Continuous fun v => P u v) :
    FactorizationAssociativityGate P :=
  factorizationGate_of_ledgerLinearResponse P
    (ledgerLinearResponse_from_primitiveLedgerPosting P h hcont)

/-- Primitive ledger posting plus continuity forces the canonical RCL
combiner. -/
theorem primitiveLedgerPosting_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hcont : ∀ u, Continuous fun v => P u v) :
    ∀ u v, P u v = rclCombiner u v :=
  ledgerLinearResponse_forces_rcl P
    (ledgerLinearResponse_from_primitiveLedgerPosting P h hcont)

/-- Primitive ledger posting plus monotone response supplies the full
factorization gate.  This is the order-regularity route: monotonicity replaces
the continuity gate. -/
theorem factorizationGate_of_primitiveLedgerPosting_monotone
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hmono : ∀ u, Monotone fun v => P u v) :
    FactorizationAssociativityGate P :=
  factorizationGate_of_ledgerLinearResponse P
    (ledgerLinearResponse_from_primitiveLedgerPosting_monotone P h hmono)

/-- Primitive ledger posting plus monotone response forces the canonical RCL
combiner.  No continuity or completeness is used: only additivity from the free
ledger and order regularity. -/
theorem primitiveLedgerPosting_monotone_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hmono : ∀ u, Monotone fun v => P u v) :
    ∀ u v, P u v = rclCombiner u v :=
  ledgerLinearResponse_forces_rcl P
    (ledgerLinearResponse_from_primitiveLedgerPosting_monotone P h hmono)

/-- Primitive ledger posting plus **ledger-native cost non-negativity** supplies
the full factorization gate.  The regularity input is the order shadow of
`ledgerCost_nonneg`, not an analytic continuity assumption. -/
theorem factorizationGate_of_primitiveLedgerPosting_nonneg
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hnn : ∀ u v, 0 ≤ v → P u 0 ≤ P u v) :
    FactorizationAssociativityGate P :=
  factorizationGate_of_ledgerLinearResponse P
    (ledgerLinearResponse_from_primitiveLedgerPosting_nonneg P h hnn)

/-- Primitive ledger posting plus **ledger-native cost non-negativity** forces the
canonical RCL combiner.  This is the fully ledger-internal route to
right-affineness: additivity comes from `ledgerCost_add`, and the only order
input is that posting non-negative defect mass never lowers cost, which is the
order shadow of `ledgerCost_nonneg`. -/
theorem primitiveLedgerPosting_nonneg_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hnn : ∀ u v, 0 ≤ v → P u 0 ≤ P u v) :
    ∀ u v, P u v = rclCombiner u v :=
  ledgerLinearResponse_forces_rcl P
    (ledgerLinearResponse_from_primitiveLedgerPosting_nonneg P h hnn)

/-- Primitive ledger posting plus **per-slice directional regularity** supplies
the full factorization gate.  This is the non-vacuous order route: the canonical
combiner satisfies the hypothesis (`rclCombiner_directional`). -/
theorem factorizationGate_of_primitiveLedgerPosting_directional
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v)) :
    FactorizationAssociativityGate P :=
  factorizationGate_of_ledgerLinearResponse P
    (ledgerLinearResponse_from_primitiveLedgerPosting_directional P h hdir)

/-- Primitive ledger posting plus **per-slice directional regularity** forces the
canonical RCL combiner.  Additivity is supplied by `ledgerCost_add`; the only
regularity input is that each fixed-cost response is monotone in one direction,
which the canonical combiner provably satisfies, so this forcing is
non-vacuous. -/
theorem primitiveLedgerPosting_directional_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : PrimitiveLedgerPostingSemantics P)
    (hdir : ∀ u, Monotone (fun v => P u v) ∨ Antitone (fun v => P u v)) :
    ∀ u v, P u v = rclCombiner u v :=
  ledgerLinearResponse_forces_rcl P
    (ledgerLinearResponse_from_primitiveLedgerPosting_directional P h hdir)

/-- **Ledger order-faithfulness anchor.** For non-negative weights the free
ledger cost never decreases when defect mass is added.  This is a direct
consequence of unconditional additivity (`ledgerCost_add`) and cost
non-negativity (`ledgerCost_nonneg`); it is the proved ledger fact whose order
shadow is the `hnn` hypothesis of the non-negativity route above. -/
theorem ledgerCost_le_add_right {I : Type} (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (Γ Δ : RecognitionLedgerFloor.DefectLedger I) :
    RecognitionLedgerFloor.ledgerCost w Γ ≤
      RecognitionLedgerFloor.ledgerCost w (Γ + Δ) := by
  rw [RecognitionLedgerFloor.ledgerCost_add]
  linarith [RecognitionLedgerFloor.ledgerCost_nonneg w hw Δ]

/-- The canonical RCL combiner satisfies the ledger-native posting
non-negativity hypothesis on the physical recognition domain `u ≥ 0`: posting
non-negative ledger mass `v` never lowers the combined cost.  Hence the
non-negativity forcing route is non-vacuous and is satisfied by the intended
combiner, with the regularity input grounded in `ledgerCost_nonneg` rather than
analytic continuity. -/
theorem rclCombiner_postingNonneg :
    ∀ u v, 0 ≤ u → 0 ≤ v → rclCombiner u 0 ≤ rclCombiner u v := by
  intro u v hu hv
  unfold rclCombiner
  nlinarith [mul_nonneg hu hv, mul_nonneg hu hv]

/-- **Non-vacuity witness for the directional route.** For each fixed first cost
`u`, the canonical RCL combiner responds to posted mass `v` monotonically in one
direction: increasing when `u ≥ -1`, decreasing when `u ≤ -1`.  This shows the
`hdir` hypothesis of `primitiveLedgerPosting_directional_forces_rcl` is satisfied
by the combiner it forces, so the order route is a genuine (non-vacuous) closure,
unlike the global-monotone and global-nonneg routes which only hold on the
physical cost cone `u ≥ 0`. -/
theorem rclCombiner_directional :
    ∀ u, Monotone (fun v => rclCombiner u v) ∨
      Antitone (fun v => rclCombiner u v) := by
  intro u
  rcases le_or_gt 0 (u + 1) with hu | hu
  · left
    intro a b hab
    unfold rclCombiner
    nlinarith [mul_nonneg hu (by linarith : (0 : ℝ) ≤ b - a)]
  · right
    intro a b hab
    unfold rclCombiner
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(u + 1)) (by linarith : (0 : ℝ) ≤ b - a)]

/-- The canonical RCL combiner has ledger-linear response. -/
theorem rclCombiner_ledgerLinearResponse :
    LedgerLinearResponse rclCombiner where
  symmetric := rclCombiner_satisfies_gate.symmetric
  zeroBoundary := rclCombiner_satisfies_gate.zeroBoundary
  unitDiagonal := rclCombiner_satisfies_gate.unitDiagonal
  rightResponse := by
    intro u v
    unfold rclCombiner
    ring
  free_ledger_additivity := by
    intro I w Γ Δ
    exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- The canonical RCL combiner carries the weaker free-ledger semantics: posted
increments add, the response is continuous, and the free ledger supplies
additivity. -/
theorem rclCombiner_freeLedgerSemantics :
    FreeLedgerCombinerSemantics rclCombiner where
  symmetric := rclCombiner_satisfies_gate.symmetric
  zeroBoundary := rclCombiner_satisfies_gate.zeroBoundary
  unitDiagonal := rclCombiner_satisfies_gate.unitDiagonal
  rightPostedAdditive := by
    intro u v w
    unfold rclCombiner
    ring
  rightContinuous := by
    intro u
    unfold rclCombiner
    continuity
  free_ledger_additivity := by
    intro I w Γ Δ
    exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- The ledger-linear response target is equivalent to the canonical RCL
polynomial.  This leaves one clean Phase 3 obligation: prove ledger-linear
response from the free ledger interpretation. -/
theorem ledgerLinearResponse_iff_rcl (P : ℝ → ℝ → ℝ) :
    LedgerLinearResponse P ↔ ∀ u v, P u v = rclCombiner u v := by
  constructor
  · exact ledgerLinearResponse_forces_rcl P
  · intro hP
    refine {
      symmetric := ?_
      zeroBoundary := ?_
      unitDiagonal := ?_
      rightResponse := ?_
      free_ledger_additivity := ?_
    }
    · intro u v
      rw [hP u v, hP v u]
      unfold rclCombiner
      ring
    · intro u
      rw [hP u 0]
      unfold rclCombiner
      ring
    · rw [hP 1 1]
      unfold rclCombiner
      norm_num
    · intro u v
      rw [hP u v, hP u 1, hP u 0]
      unfold rclCombiner
      ring
    · intro I w Γ Δ
      exact RecognitionLedgerFloor.ledgerCost_add w Γ Δ

/-- Rational completed ledger posting supplies the full factorization gate. -/
theorem factorizationGate_of_rationalLedgerPosting
    (P : ℝ → ℝ → ℝ) (h : RationalLedgerPostingSemantics P) :
    FactorizationAssociativityGate P :=
  factorizationGate_of_ledgerLinearResponse P
    ((rationalLedgerPosting_iff_ledgerLinearResponse P).1 h)

/-- Rational completed ledger posting forces the canonical RCL polynomial. -/
theorem rationalLedgerPosting_forces_rcl
    (P : ℝ → ℝ → ℝ) (h : RationalLedgerPostingSemantics P) :
    ∀ u v, P u v = rclCombiner u v :=
  ledgerLinearResponse_forces_rcl P
    ((rationalLedgerPosting_iff_ledgerLinearResponse P).1 h)

/-- Rational completed ledger posting is exactly equivalent to being the
canonical RCL combiner. -/
theorem rationalLedgerPosting_iff_rcl (P : ℝ → ℝ → ℝ) :
    RationalLedgerPostingSemantics P ↔ ∀ u v, P u v = rclCombiner u v := by
  constructor
  · exact rationalLedgerPosting_forces_rcl P
  · intro hP
    exact (rationalLedgerPosting_iff_ledgerLinearResponse P).2
      ((ledgerLinearResponse_iff_rcl P).2 hP)

/-- Free-ledger posting semantics and rational completed ledger posting are the
same completed T5 semantic bridge. -/
theorem freeLedgerCombinerSemantics_iff_rationalLedgerPosting
    (P : ℝ → ℝ → ℝ) :
    FreeLedgerCombinerSemantics P ↔ RationalLedgerPostingSemantics P := by
  constructor
  · intro h
    exact (rationalLedgerPosting_iff_ledgerLinearResponse P).2
      ((freeLedgerCombinerSemantics_iff_ledgerLinearResponse P).1 h)
  · intro h
    exact (freeLedgerCombinerSemantics_iff_ledgerLinearResponse P).2
      ((rationalLedgerPosting_iff_ledgerLinearResponse P).1 h)

/-- Free-ledger posting semantics is exactly equivalent to being the canonical
RCL combiner. -/
theorem freeLedgerCombinerSemantics_iff_rcl (P : ℝ → ℝ → ℝ) :
    FreeLedgerCombinerSemantics P ↔ ∀ u v, P u v = rclCombiner u v := by
  constructor
  · intro h
    exact ledgerLinearResponse_forces_rcl P
      ((freeLedgerCombinerSemantics_iff_ledgerLinearResponse P).1 h)
  · intro hP
    exact (freeLedgerCombinerSemantics_iff_ledgerLinearResponse P).2
      ((ledgerLinearResponse_iff_rcl P).2 hP)

end LedgerToFactorization
end Foundation
end IndisputableMonolith
