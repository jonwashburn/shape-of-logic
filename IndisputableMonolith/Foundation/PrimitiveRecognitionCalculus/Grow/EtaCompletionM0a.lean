/-
  PrimitiveRecognitionCalculus/Grow/EtaCompletionM0a.lean

  M0a: the constructive-real carrier ℝδ_pre as Bishop regular sequences over the
  δ-rationals, and the unit map η : ℚδ → ℝδ_pre.

  A regular sequence is a rule `(a_n)` of δ-rationals with
  `|a_m - a_n| ≤ 1/(m+1) + 1/(n+1)`, expressed purely at the integer
  cross-multiplication level (no ℚ display), so the whole construction stays on
  the `{propext, Quot.sound}` axiom basis (audit tier FORCED). The equivalence
  `equiv s t` is "the pointwise difference converges to 0", again integer-level.

  Provenance. The carrier (`crossDiff`, `RegularSeq`, `equiv`, `eta`,
  `eta_regular`, `equiv_refl`, `eta_respects_crossEq`) was first synthesized by the
  `delta_grow` autonomous loop (GLM-5.2 maker, lake + `#print axioms` judge) and
  accepted choice-free. This module promotes that artifact into the library and
  completes it: `equiv_symm` and `equiv_trans` (the choice-free triangle
  argument) make `equivSetoid` a genuine setoid; `RealDelta := Quot equivSetoid`
  is the M0a real line; `etaQ : PRCRat → RealDelta` is the unit descended
  through both quotients; and `etaQ_injective` (via the Archimedean step
  `crossEq_of_equiv_eta`) makes it an embedding. Verified 2026-07-02: every
  declaration here has axiom closure exactly `{propext, Quot.sound}`, i.e.
  audit tier FORCED, strictly below the NAMED(AC_ω) cost the north-star verdict
  budgeted for this rung. The AC_ω completeness rung (limit existence, the
  NAMED-tier claim) sits on top of this setoid and is tracked separately.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerRational
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.IntegerOrder

namespace IndisputableMonolith.PRCGrow.EtaCompletionM0a

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus

/-- The cross-difference: the integer numerator of `a - b`,
i.e., `a.num * b.den - b.num * a.den`. This avoids the ℚ display entirely. -/
def crossDiff (a b : RatioOrbit) : ℤ :=
  a.num.toInt * (b.den.toNat : ℤ) - b.num.toInt * (a.den.toNat : ℤ)

/-- A rational minus itself has zero cross-difference. -/
theorem crossDiff_self (a : RatioOrbit) : crossDiff a a = 0 := by
  unfold crossDiff
  omega

/-- Cross-equal rationals have zero cross-difference. -/
theorem crossDiff_of_crossEq (a b : RatioOrbit) (h : RatioOrbit.crossEq a b) :
    crossDiff a b = 0 := by
  rw [RatioOrbit.crossEq_iff_toIntCross] at h
  unfold crossDiff
  omega

/-- Antisymmetry of the cross-difference: `crossDiff b a = -crossDiff a b`. -/
theorem crossDiff_swap (a b : RatioOrbit) : crossDiff b a = -crossDiff a b := by
  unfold crossDiff
  ring

/-- The three-point cross-difference identity, the algebraic backbone of the
triangle inequality. As rationals `(a-c) = (a-b) + (b-c)`; clearing the three
denominators gives this pure integer identity:
`crossDiff a c * den b = crossDiff a b * den c + crossDiff b c * den a`. -/
theorem crossDiff_triangle_id (a b c : RatioOrbit) :
    crossDiff a c * (b.den.toNat : ℤ) =
      crossDiff a b * (c.den.toNat : ℤ) + crossDiff b c * (a.den.toNat : ℤ) := by
  unfold crossDiff
  ring

/-- A regular sequence of delta-rationals.

A sequence `(a_n)` is regular when `|a_m - a_n| ≤ 1/(m+1) + 1/(n+1)` for all `m, n`.
Expressed via integer cross-multiplication (avoiding the ℚ display):
`|crossDiff(a_m, a_n)| * (m+1) * (n+1) ≤ (m+n+2) * den(a_m) * den(a_n)`. -/
structure RegularSeq where
  seq : ℕ → RatioOrbit
  regular : ∀ m n : ℕ,
    Int.natAbs (crossDiff (seq m) (seq n)) * (m + 1) * (n + 1) ≤
    (m + n + 2) * (seq m).den.toNat * (seq n).den.toNat

/-- Working equality on regular sequences: their pointwise difference
converges to 0. For every tolerance `1/(k+1)`, eventually
`|s_n - t_n| ≤ 1/(k+1)`. -/
def equiv (s t : RegularSeq) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    Int.natAbs (crossDiff (s.seq n) (t.seq n)) * (k + 1) ≤
    (s.seq n).den.toNat * (t.seq n).den.toNat

/-- Well-formedness of `eta`: the constant sequence satisfies regularity. -/
theorem eta_regular (q : RatioOrbit) (m n : ℕ) :
  Int.natAbs (crossDiff q q) * (m + 1) * (n + 1) ≤
  (m + n + 2) * q.den.toNat * q.den.toNat := by
  rw [crossDiff_self, Int.natAbs_zero, Nat.zero_mul, Nat.zero_mul]
  exact Nat.zero_le _

/-- The unit map: embed a delta-rational as a constant regular sequence. -/
def eta (q : RatioOrbit) : RegularSeq :=
  ⟨fun _ => q, fun m n => eta_regular q m n⟩

/-- The sequence of `eta q` is the constant sequence `q`. -/
theorem eta_seq (q : RatioOrbit) (n : ℕ) : (eta q).seq n = q := by
  rfl

/-- `equiv` is reflexive: every regular sequence is equivalent to itself. -/
theorem equiv_refl (s : RegularSeq) : equiv s s := by
  intro k
  refine ⟨0, ?_⟩
  intro n _
  rw [crossDiff_self, Int.natAbs_zero, Nat.zero_mul]
  exact Nat.zero_le _

/-- `equiv` is symmetric. The cross-difference only flips sign, so its absolute
value and the denominator product are unchanged. Choice-free. -/
theorem equiv_symm {s t : RegularSeq} (h : equiv s t) : equiv t s := by
  intro k
  obtain ⟨N, hN⟩ := h k
  refine ⟨N, ?_⟩
  intro n hn
  have hcd : crossDiff (t.seq n) (s.seq n) = -crossDiff (s.seq n) (t.seq n) :=
    crossDiff_swap (s.seq n) (t.seq n)
  rw [hcd, Int.natAbs_neg, Nat.mul_comm (t.seq n).den.toNat (s.seq n).den.toNat]
  exact hN n hn

/-- `equiv` is transitive: the choice-free triangle argument at the integer
cross-multiplication level. From `|s_n - t_n| ≤ 1/(2k+2)` and
`|t_n - u_n| ≤ 1/(2k+2)` eventually, the three-point identity plus positivity of
the middle denominator give `|s_n - u_n| ≤ 1/(k+1)`, with no ℚ display (so the
proof stays on `{propext, Quot.sound}`). -/
theorem equiv_trans {s t u : RegularSeq}
    (hst : equiv s t) (htu : equiv t u) : equiv s u := by
  intro k
  obtain ⟨N₁, hN₁⟩ := hst (2 * k + 1)
  obtain ⟨N₂, hN₂⟩ := htu (2 * k + 1)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : n ≥ N₁ := le_trans (Nat.le_max_left N₁ N₂) hn
  have hn₂ : n ≥ N₂ := le_trans (Nat.le_max_right N₁ N₂) hn
  -- The three participating rationals at index n.
  set A := s.seq n with hA
  set B := t.seq n with hB
  set C := u.seq n with hC
  -- Hypotheses at level 2k+1 (i.e. factor 2k+1+1), in Nat. `set` rewrote the
  -- goal but not the ∀-hypotheses, so re-fold `s.seq n → A` etc. by hand.
  have h1 : (crossDiff A B).natAbs * (2 * k + 1 + 1) ≤ A.den.toNat * B.den.toNat := by
    have h := hN₁ n hn₁; rw [← hA, ← hB] at h; exact h
  have h2 : (crossDiff B C).natAbs * (2 * k + 1 + 1) ≤ B.den.toNat * C.den.toNat := by
    have h := hN₂ n hn₂; rw [← hB, ← hC] at h; exact h
  -- Positive denominators.
  have hdBpos : 0 < B.den.toNat := Nat.pos_of_ne_zero B.den_toNat_ne_zero
  -- Triangle in Nat via the integer identity and `Int.natAbs_add_le`.
  have hid : crossDiff A C * (B.den.toNat : ℤ) =
      crossDiff A B * (C.den.toNat : ℤ) + crossDiff B C * (A.den.toNat : ℤ) :=
    crossDiff_triangle_id A B C
  have heq := congrArg Int.natAbs hid
  have hnatB : ((B.den.toNat : ℤ)).natAbs = B.den.toNat := Int.natAbs_natCast _
  have hnatC : ((C.den.toNat : ℤ)).natAbs = C.den.toNat := Int.natAbs_natCast _
  have hnatA : ((A.den.toNat : ℤ)).natAbs = A.den.toNat := Int.natAbs_natCast _
  have hL : (crossDiff A C * (B.den.toNat : ℤ)).natAbs
      = (crossDiff A C).natAbs * B.den.toNat := by
    rw [Int.natAbs_mul, hnatB]
  have hR : (crossDiff A B * (C.den.toNat : ℤ) + crossDiff B C * (A.den.toNat : ℤ)).natAbs
      ≤ (crossDiff A B).natAbs * C.den.toNat + (crossDiff B C).natAbs * A.den.toNat := by
    refine le_trans (Int.natAbs_add_le _ _) ?_
    rw [Int.natAbs_mul, Int.natAbs_mul, hnatC, hnatA]
  have htriN : (crossDiff A C).natAbs * B.den.toNat
      ≤ (crossDiff A B).natAbs * C.den.toNat + (crossDiff B C).natAbs * A.den.toNat := by
    rw [hL] at heq; rw [heq]; exact hR
  -- Do the ε/2 arithmetic entirely in ℕ, using only monotone product lemmas and
  -- `ring`/`omega` (all choice-free). Casting to ℤ via norm_cast smuggles
  -- `Classical.choice` here, so we stay in ℕ.
  set cAC := (crossDiff A C).natAbs with hcAC
  set cAB := (crossDiff A B).natAbs with hcAB
  set cBC := (crossDiff B C).natAbs with hcBC
  set dA := A.den.toNat with hdA
  set dB := B.den.toNat with hdB
  set dC := C.den.toNat with hdC
  set two := 2 * k + 1 + 1 with htwo_def
  -- htriN : cAC*dB ≤ cAB*dC + cBC*dA ;  h1 : cAB*two ≤ dA*dB ;  h2 : cBC*two ≤ dB*dC
  have e1 : cAB * two * dC ≤ dA * dB * dC := Nat.mul_le_mul_right dC h1
  have e2 : cBC * two * dA ≤ dB * dC * dA := Nat.mul_le_mul_right dA h2
  have base : cAC * dB * two ≤ (cAB * dC + cBC * dA) * two := Nat.mul_le_mul_right two htriN
  have expand : (cAB * dC + cBC * dA) * two = cAB * two * dC + cBC * two * dA := by ring
  have chain : cAC * dB * two ≤ dA * dB * dC + dB * dC * dA := by
    rw [expand] at base; exact le_trans base (add_le_add e1 e2)
  -- two = 2*(k+1); repackage both sides around the common positive factor 2*dB.
  have htwo : two = 2 * (k + 1) := by rw [htwo_def]; ring
  have lhs_eq : cAC * dB * two = cAC * (k + 1) * (2 * dB) := by rw [htwo]; ring
  have rhs_eq : dA * dB * dC + dB * dC * dA = dA * dC * (2 * dB) := by ring
  have cancel_in : cAC * (k + 1) * (2 * dB) ≤ dA * dC * (2 * dB) := by
    rw [← lhs_eq, ← rhs_eq]; exact chain
  have hpos : 0 < 2 * dB := by rw [hdB]; omega
  exact Nat.le_of_mul_le_mul_right cancel_in hpos

/-- `eta` respects `crossEq`: if `q` and `r` are cross-equal (represent the same
delta-rational), then `eta q` and `eta r` are equivalent regular sequences.
This is the key well-definedness property of the unit map. -/
theorem eta_respects_crossEq (q r : RatioOrbit) (h : RatioOrbit.crossEq q r) :
  equiv (eta q) (eta r) := by
  intro k
  refine ⟨0, ?_⟩
  intro n _
  rw [eta_seq q n, eta_seq r n, crossDiff_of_crossEq q r h,
    Int.natAbs_zero, Nat.zero_mul]
  exact Nat.zero_le _

/-- `equiv` is an equivalence relation: reflexive, symmetric, transitive. This is
the completion of the M0a carrier into a genuine setoid, all choice-free. -/
theorem equiv_equivalence : Equivalence equiv where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The M0a real setoid: regular sequences of δ-rationals modulo pointwise
convergence to zero. The quotient `Quot equivSetoid` is the constructive real
line ℝδ_pre; `eta` descends to the rational embedding on it. -/
def equivSetoid : Setoid RegularSeq where
  r := equiv
  iseqv := equiv_equivalence

/-- The M0a constructive real line ℝδ_pre: regular sequences of δ-rationals
modulo pointwise convergence to zero. Built with `Quot` only, so the carrier
sits on `{propext, Quot.sound}` (audit tier FORCED). -/
def RealDelta : Type :=
  Quot equivSetoid

namespace RealDelta

/-- Constructor from a regular-sequence display. -/
def mk (s : RegularSeq) : RealDelta :=
  Quot.mk equivSetoid s

/-- Equivalent regular sequences determine equal constructive reals. -/
theorem mk_eq_mk_of_equiv {s t : RegularSeq} (h : equiv s t) : mk s = mk t :=
  Quot.sound h

end RealDelta

/-- The unit map η : ℚδ → ℝδ_pre, descended through both quotients: a PRC
rational (ratio orbit modulo cross-equality) maps to the class of its constant
regular sequence. Well-definedness is `eta_respects_crossEq`. This is the M0a
carrier morphism of the Forced ⊣ Classical adjunction program. -/
def etaQ : PRCRat → RealDelta :=
  Quot.lift (fun q => RealDelta.mk (eta q))
    (fun q r h => RealDelta.mk_eq_mk_of_equiv (eta_respects_crossEq q r h))

/-- `etaQ` on a display rational is the class of the constant sequence. -/
@[simp] theorem etaQ_mk (q : RatioOrbit) :
    etaQ (PRCRat.mk q) = RealDelta.mk (eta q) := rfl

/-- The Archimedean step: if the constant sequences at `q` and `r` are
equivalent (their fixed difference is below every `1/(k+1)`), then `q` and `r`
are cross-equal. Instantiate the tolerance at `k = den q * den r`; then
`c * (k+1) ≤ k` forces `c = 0`. Choice-free. -/
theorem crossEq_of_equiv_eta {q r : RatioOrbit}
    (h : equiv (eta q) (eta r)) : RatioOrbit.crossEq q r := by
  set k := q.den.toNat * r.den.toNat with hk
  obtain ⟨N, hN⟩ := h k
  have hbound := hN N (Nat.le_refl N)
  rw [eta_seq q N, eta_seq r N, ← hk] at hbound
  -- hbound : |crossDiff q r| * (k+1) ≤ k, so |crossDiff q r| = 0.
  have hzero : (crossDiff q r).natAbs = 0 := by
    by_contra hne
    have hone : 1 ≤ (crossDiff q r).natAbs := Nat.pos_of_ne_zero hne
    have : k + 1 ≤ (crossDiff q r).natAbs * (k + 1) := by
      calc k + 1 = 1 * (k + 1) := (Nat.one_mul _).symm
        _ ≤ (crossDiff q r).natAbs * (k + 1) := Nat.mul_le_mul_right (k + 1) hone
    exact absurd (le_trans this hbound) (by omega)
  have hcd : crossDiff q r = 0 := Int.natAbs_eq_zero.mp hzero
  rw [RatioOrbit.crossEq_iff_toIntCross]
  unfold crossDiff at hcd
  omega

/-- The unit η : ℚδ → ℝδ_pre is injective: no two distinct δ-rationals collapse
in the completion. Together with well-definedness this makes η a genuine
embedding of the rational base into the M0a real line, choice-free. -/
theorem etaQ_injective : Function.Injective etaQ := by
  intro a b h
  induction a using Quot.ind with
  | mk q =>
    induction b using Quot.ind with
    | mk r =>
      have hq : RealDelta.mk (eta q) = RealDelta.mk (eta r) := h
      have hequiv : equiv (eta q) (eta r) := by
        have := Quot.eqvGen_exact hq
        -- Exactness gives `EqvGen`; collapse it with the proved equivalence.
        exact (Equivalence.eqvGen_iff equiv_equivalence).mp this
      exact Quot.sound (crossEq_of_equiv_eta hequiv)

end IndisputableMonolith.PRCGrow.EtaCompletionM0a
