import Mathlib
import IndisputableMonolith.Foundation.DeltaSpine.GoldenInt
import IndisputableMonolith.Foundation.DeltaSpine.CostUniqueness
import IndisputableMonolith.Foundation.DeltaSpine.LadderRatioBounds
import IndisputableMonolith.Foundation.PhiForcing
import IndisputableMonolith.Cost

/-!
# GoldenIntReal: the display bridge from ℤ[φ] to ℝ

**The sigma1 boundary module.** `DeltaSpine.GoldenInt` derives T6 (φ forced as
the unique positive golden root) entirely inside ℤ[φ], with axiom closure
`{propext, Quot.sound}` (sigma0 DELTA_FORCED). This module pays the continuum
tax exactly once, at the display boundary: it evaluates ℤ[φ] into ℝ and shows
the sigma0 structure maps onto the classical `PhiForcing` presentation.

Contents:
* `toReal : GoldenInt → ℝ`, the evaluation `a + b·φ ↦ a + b·φℝ`;
* `toReal` is a ring embedding (additive, multiplicative via `φ² = φ + 1`,
  injective via the irrationality descent `int_sq_eq_five_sq`);
* `toReal phi = PhiForcing.φ`: the sigma0 φ is the classical φ;
* `isPos_iff_toReal_pos`: the decidable integer sign predicate `IsPos` is
  exactly real positivity — so the sigma0 trichotomy/uniqueness theorems are
  about the real order, not a private surrogate;
* `t6_bridge`: the unique positive golden root of the sigma0 derivation
  evaluates to `(1 + √5)/2`.

This module is honestly **sigma1 CHOICE** (`Real.sqrt`, `nlinarith` over ℝ).
That is the point: the *derivation* is delta-forced; only the *display* into
the continuum costs `Classical.choice`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine

open GoldenInt

/-- Evaluation of ℤ[φ] into ℝ: `⟨a, b⟩ ↦ a + b·φ`. -/
noncomputable def toReal (x : GoldenInt) : ℝ :=
  (x.a : ℝ) + (x.b : ℝ) * PhiForcing.φ

@[simp] theorem toReal_zero : toReal 0 = 0 := by simp [toReal]

@[simp] theorem toReal_one : toReal 1 = 1 := by simp [toReal]

/-- The sigma0 φ evaluates to the classical golden ratio. -/
@[simp] theorem toReal_phi : toReal GoldenInt.phi = PhiForcing.φ := by
  simp [toReal, GoldenInt.phi]

/-- The sigma0 conjugate root evaluates to `1 − φ = (1 − √5)/2`. -/
@[simp] theorem toReal_psi : toReal GoldenInt.psi = 1 - PhiForcing.φ := by
  simp [toReal, GoldenInt.psi]; ring

theorem toReal_add (x y : GoldenInt) : toReal (x + y) = toReal x + toReal y := by
  simp only [toReal, add_a, add_b]
  push_cast
  ring

theorem toReal_neg (x : GoldenInt) : toReal (-x) = -toReal x := by
  simp only [toReal, neg_a, neg_b]
  push_cast
  ring

/-- Multiplicativity: the ℤ[φ] product law *is* multiplication in ℝ, because
    `φ² = φ + 1` (`PhiForcing.phi_equation`). -/
theorem toReal_mul (x y : GoldenInt) : toReal (x * y) = toReal x * toReal y := by
  simp only [toReal, mul_a, mul_b]
  push_cast
  -- the ℤ[φ] product law is exactly multiplication in ℝ because φ² = φ + 1
  linear_combination (-(x.b : ℝ) * (y.b : ℝ)) * PhiForcing.phi_equation

/-- `toReal` kills only 0 — the irrationality of √5 again, imported from the
    sigma0 descent lemma `int_sq_eq_five_sq`. -/
theorem toReal_eq_zero_iff {x : GoldenInt} : toReal x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hss : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
    -- 2·toReal x = (2a + b) + b·√5
    have h2 : ((2 * x.a + x.b : ℤ) : ℝ) + (x.b : ℝ) * Real.sqrt 5 = 0 := by
      have hφ : PhiForcing.φ = (1 + Real.sqrt 5) / 2 := rfl
      rw [toReal, hφ] at h
      push_cast
      linarith
    have hs : ((2 * x.a + x.b : ℤ) : ℝ) = -(x.b : ℝ) * Real.sqrt 5 := by linarith
    have hsqR : ((2 * x.a + x.b : ℤ) : ℝ) * ((2 * x.a + x.b : ℤ) : ℝ)
        = 5 * ((x.b : ℝ) * (x.b : ℝ)) := by
      rw [hs]
      nlinarith [hss]
    have hsqZ : (2 * x.a + x.b) * (2 * x.a + x.b) = 5 * (x.b * x.b) := by
      exact_mod_cast hsqR
    have hb : x.b = 0 := GoldenInt.int_sq_eq_five_sq hsqZ
    have ha : x.a = 0 := by
      have h2' := h2
      rw [hb] at h2'
      push_cast at h2'
      have : (x.a : ℝ) = 0 := by linarith
      exact_mod_cast this
    ext
    · rw [ha]; rfl
    · rw [hb]; rfl
  · rintro rfl
    exact toReal_zero

theorem toReal_injective : Function.Injective toReal := by
  intro x y h
  have hz : toReal (x + -y) = 0 := by
    rw [toReal_add, toReal_neg, h]
    ring
  have hxy : x + -y = 0 := toReal_eq_zero_iff.mp hz
  have : x = y := by
    have := congrArg (· + y) hxy
    simpa [add_assoc, add_comm, add_left_comm] using this
  exact this

/-- The pair predicate `PosPair s t` says exactly `0 < s + t·√5`. Forward
    direction of the sign bridge. -/
theorem posPair_real_pos {s t : ℤ} (h : PosPair s t) :
    0 < (s : ℝ) + (t : ℝ) * Real.sqrt 5 := by
  have hss : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rcases h with ⟨hs, ht, hst⟩ | ⟨hs, ht, hq⟩ | ⟨hs, ht, hq⟩
  · -- both nonnegative, one strictly positive
    have hs' : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
    have ht' : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    rcases hst with h' | h'
    · have : (0 : ℝ) < (s : ℝ) := by exact_mod_cast h'
      nlinarith
    · have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast h'
      nlinarith
  · -- s < 0 < t, dominated: s² < 5t²
    have hs' : (s : ℝ) < 0 := by exact_mod_cast hs
    have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hq' : (s : ℝ) * (s : ℝ) < 5 * ((t : ℝ) * (t : ℝ)) := by exact_mod_cast hq
    by_contra hle
    push_neg at hle
    have h1 : (t : ℝ) * Real.sqrt 5 ≤ -(s : ℝ) := by linarith
    have h2 : (0 : ℝ) < (t : ℝ) * Real.sqrt 5 := mul_pos ht' hpos
    nlinarith
  · -- t < 0 < s, dominated: 5t² < s²
    have hs' : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have ht' : (t : ℝ) < 0 := by exact_mod_cast ht
    have hq' : 5 * ((t : ℝ) * (t : ℝ)) < (s : ℝ) * (s : ℝ) := by exact_mod_cast hq
    by_contra hle
    push_neg at hle
    have h1 : (s : ℝ) ≤ -(t : ℝ) * Real.sqrt 5 := by linarith
    have h2 : (0 : ℝ) < -(t : ℝ) * Real.sqrt 5 := by
      apply mul_pos _ hpos
      linarith
    nlinarith

/-- **The sign bridge**: the sigma0 decidable predicate `IsPos` is exactly real
    positivity of the evaluation. Proved via the sigma0 trichotomy — the
    forward direction is `posPair_real_pos`; the reverse uses exclusivity
    (`isPos_not_neg`) so no real-side case analysis is ever needed. -/
theorem isPos_iff_toReal_pos (x : GoldenInt) : IsPos x ↔ 0 < toReal x := by
  have key : ∀ y : GoldenInt, IsPos y → 0 < toReal y := by
    intro y hy
    have h := posPair_real_pos hy
    have hφ : PhiForcing.φ = (1 + Real.sqrt 5) / 2 := rfl
    rw [toReal, hφ]
    push_cast at h ⊢
    linarith
  constructor
  · exact key x
  · intro h
    rcases isPos_trichotomy x with hp | hz | hn
    · exact hp
    · exfalso
      rw [hz, toReal_zero] at h
      exact lt_irrefl 0 h
    · exfalso
      have hneg := key (-x) hn
      rw [toReal_neg] at hneg
      linarith

/-- **T6 display bridge**: the unique positive golden root delivered by the
    sigma0 derivation is, under evaluation, the classical `(1 + √5)/2`. The
    mathematical work (uniqueness, positivity, the two roots) was all done at
    sigma0; this theorem only translates it. -/
theorem t6_bridge :
    toReal GoldenInt.phi = (1 + Real.sqrt 5) / 2 ∧
    0 < toReal GoldenInt.phi ∧
    toReal GoldenInt.phi * toReal GoldenInt.phi = toReal GoldenInt.phi + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toReal_phi]; rfl
  · exact (isPos_iff_toReal_pos GoldenInt.phi).mp GoldenInt.phi_isPos
  · rw [← toReal_mul, GoldenInt.phi_sq, toReal_add, toReal_one]

/-! ## T5 display bridge

`DeltaSpine.CostUniqueness` derives the T5 cost-uniqueness content at sigma0:
the trace sequence `traceZ n = φⁿ + φ⁻ⁿ` is the unique solution of the
d'Alembert law with the forced initial conditions, and `Jdouble n = traceZ n − 2`
is the unique solution of the discrete Recognition Composition Law. This
section evaluates those objects into ℝ and shows they are exactly the
classical presentation: `traceZ` is `2·cosh(n·log φ)` and `Jdouble` is
`2·Jcost(φⁿ)` for the canonical cost `Jcost x = (x + x⁻¹)/2 − 1` of
`Cost.FunctionalEquation`. Again: the forcing was done at sigma0; this is
display only. -/

theorem toReal_sub (x y : GoldenInt) : toReal (x - y) = toReal x - toReal y := by
  rw [sub_eq_add_neg, toReal_add, toReal_neg]
  ring

theorem toReal_two : toReal 2 = 2 := by
  have h : (2 : GoldenInt) = ⟨2, 0⟩ := by decide
  rw [h]
  show ((2 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * PhiForcing.φ = 2
  push_cast
  ring

/-- The sigma0 inverse `phiInv = φ − 1` evaluates to the real `φ⁻¹`. -/
theorem toReal_phiInv : toReal GoldenInt.phiInv = PhiForcing.φ⁻¹ := by
  have h := toReal_mul GoldenInt.phi GoldenInt.phiInv
  rw [GoldenInt.phi_mul_phiInv, toReal_one, toReal_phi] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The unit-group power ladder evaluates to real integer powers of φ. -/
theorem toReal_phiZpow (n : ℤ) : toReal (phiZpow n) = PhiForcing.φ ^ n := by
  have hφne : PhiForcing.φ ≠ 0 := ne_of_gt PhiForcing.phi_pos
  induction n using Int.induction_on with
  | zero => rw [phiZpow_zero, toReal_one, zpow_zero]
  | succ k ih =>
      have hstep : phiZpow ((k : ℤ) + 1) = phiZpow (k : ℤ) * GoldenInt.phi := by
        rw [phiZpow_add, phiZpow_one]
      rw [hstep, toReal_mul, ih, toReal_phi, ← zpow_add_one₀ hφne]
  | pred k ih =>
      have hstep : phiZpow (-(k : ℤ) - 1) = phiZpow (-(k : ℤ)) * GoldenInt.phiInv := by
        have e : -(k : ℤ) - 1 = -(k : ℤ) + (-1) := by ring
        rw [e, phiZpow_add, phiZpow_neg_one]
      rw [hstep, toReal_mul, ih, toReal_phiInv, ← zpow_sub_one₀ hφne]

/-- The sigma0 trace sequence is the classical two-sided power sum. -/
theorem toReal_traceZ (n : ℤ) :
    toReal (traceZ n) = PhiForcing.φ ^ n + PhiForcing.φ ^ (-n) := by
  show toReal (phiZpow n + phiZpow (-n)) = _
  rw [toReal_add, toReal_phiZpow, toReal_phiZpow]

/-- **The cosh display**: `traceZ n` is `2·cosh(n·log φ)`. The d'Alembert
    functional equation proved at sigma0 is the addition law of cosh. -/
theorem traceZ_cosh (n : ℤ) :
    toReal (traceZ n) = 2 * Real.cosh ((n : ℝ) * Real.log PhiForcing.φ) := by
  have hzpow : ∀ m : ℤ, PhiForcing.φ ^ m
      = Real.exp ((m : ℝ) * Real.log PhiForcing.φ) := by
    intro m
    rw [← Real.rpow_intCast PhiForcing.φ m,
        Real.rpow_def_of_pos PhiForcing.phi_pos, mul_comm]
  have e : ((-n : ℤ) : ℝ) * Real.log PhiForcing.φ
      = -((n : ℝ) * Real.log PhiForcing.φ) := by
    push_cast
    ring
  rw [toReal_traceZ, hzpow n, hzpow (-n), e, Real.cosh_eq]
  ring

/-- **The Jcost display**: the sigma0 doubled cost `Jdouble n` evaluates to
    `2·Jcost(φⁿ)` for the canonical cost `Jcost x = (x + x⁻¹)/2 − 1`. The
    discrete RCL proved at sigma0 is the composition law that forces `Jcost`
    in `Cost.FunctionalEquation`. -/
theorem jdouble_eq_jcost (n : ℤ) :
    toReal (Jdouble n) = 2 * Cost.Jcost (PhiForcing.φ ^ n) := by
  have hφne : PhiForcing.φ ≠ 0 := ne_of_gt PhiForcing.phi_pos
  show toReal (traceZ n - 2) = _
  rw [toReal_sub, toReal_traceZ, toReal_two, Cost.Jcost, zpow_neg]
  ring

/-- **T5 display bridge**, the capstone: the sigma0-forced cost ladder is,
    under evaluation, exactly the classical J-cost on the φ-ladder together
    with its cosh form. Everything with mathematical content (existence,
    uniqueness, the composition law) was proved at sigma0 in
    `DeltaSpine.CostUniqueness`; this theorem is pure translation. -/
theorem t5_bridge :
    (∀ n : ℤ, toReal (Jdouble n) = 2 * Cost.Jcost (PhiForcing.φ ^ n)) ∧
    (∀ n : ℤ, toReal (traceZ n)
      = 2 * Real.cosh ((n : ℝ) * Real.log PhiForcing.φ)) :=
  ⟨jdouble_eq_jcost, traceZ_cosh⟩

/-! ## Ladder-ratio bracket bridge

`DeltaSpine.LadderRatioBounds` pins φ and the ladder rungs φ⁵, φ⁸ inside
explicit rational intervals entirely at sigma0: the predicates `RatLt`/`RatGt`
are decidable integer sign questions on ℤ[φ] and every bracket closes by
kernel `decide`. This section is the sigma1 reading: those integer predicates
mean exactly the real inequalities they claim (`RatLt p q x` with `q > 0` is
`p/q < toReal x`, dually for `RatGt`), so the sigma0 brackets are genuine
bounds on the classical golden ratio and its powers. -/

/-- The bracket witness `q·x − p` evaluates to the real affine form. -/
theorem toReal_ratWitness (p q : ℤ) (x : GoldenInt) :
    toReal (ratWitness p q x) = (q : ℝ) * toReal x - (p : ℝ) := by
  show ((q * x.a - p : ℤ) : ℝ) + ((q * x.b : ℤ) : ℝ) * PhiForcing.φ = _
  rw [toReal]
  push_cast
  ring

/-- The sigma0 predicate `RatLt p q x` (for `q > 0`) is the real inequality
    `p/q < toReal x`. -/
theorem ratLt_toReal {p q : ℤ} {x : GoldenInt} (hq : 0 < q) (h : RatLt p q x) :
    (p : ℝ) / (q : ℝ) < toReal x := by
  have hpos := (isPos_iff_toReal_pos _).mp h
  rw [toReal_ratWitness] at hpos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [div_lt_iff₀ hq']
  nlinarith

/-- The sigma0 predicate `RatGt p q x` (for `q > 0`) is the real inequality
    `toReal x < p/q`. -/
theorem ratGt_toReal {p q : ℤ} {x : GoldenInt} (hq : 0 < q) (h : RatGt p q x) :
    toReal x < (p : ℝ) / (q : ℝ) := by
  have hpos := (isPos_iff_toReal_pos _).mp h
  rw [toReal_ratWitness, toReal_neg] at hpos
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  rw [lt_div_iff₀ hq']
  push_cast at hpos
  nlinarith

/-- The computable ℕ-ladder `phiPow` evaluates to real powers of φ. -/
theorem toReal_phiPow (n : ℕ) : toReal (phiPow n) = PhiForcing.φ ^ n := by
  rw [phiPow_eq_phiZpow, toReal_phiZpow, zpow_natCast]

/-- **Ladder-ratio display bridge**: the sigma0 rational brackets on the
    primitive forced ratio φ and the ladder rungs φ⁵, φ⁸ read, under
    evaluation, as genuine real inequalities on the classical golden ratio.
    The arithmetic was decided at sigma0 (`ladder_ratio_brackets`); this
    theorem only translates it into ℝ. -/
theorem ladder_ratio_real_brackets :
    ((1618033 : ℝ) / 1000000 < PhiForcing.φ ∧
      PhiForcing.φ < (1618034 : ℝ) / 1000000) ∧
    ((1109 : ℝ) / 100 < PhiForcing.φ ^ (5 : ℕ) ∧
      PhiForcing.φ ^ (5 : ℕ) < (1110 : ℝ) / 100) ∧
    ((46978 : ℝ) / 1000 < PhiForcing.φ ^ (8 : ℕ) ∧
      PhiForcing.φ ^ (8 : ℕ) < (46979 : ℝ) / 1000) := by
  have h1 := ratLt_toReal (by norm_num) phi_lower
  have h2 := ratGt_toReal (by norm_num) phi_upper
  have h3 := ratLt_toReal (by norm_num) phi5_lower
  have h4 := ratGt_toReal (by norm_num) phi5_upper
  have h5 := ratLt_toReal (by norm_num) phi8_lower
  have h6 := ratGt_toReal (by norm_num) phi8_upper
  rw [toReal_phi] at h1 h2
  rw [toReal_phiPow] at h3 h4 h5 h6
  push_cast at h1 h2 h3 h4 h5 h6
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩

end DeltaSpine
end Foundation
end IndisputableMonolith
