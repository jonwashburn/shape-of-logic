import IndisputableMonolith.Foundation.DeltaSpine.GoldenInt
import IndisputableMonolith.Foundation.DeltaSpine.CostUniqueness

/-!
# LadderRatioBounds: forced φ-ladder ratios with certified rational brackets (sigma0)

**One dimensionless forced ratio, carried end-to-end at sigma0, with rational
bounds that both the kernel (`decide`) and the runtime (`#eval`) certify.**

The RS mass law places every rung of the spectrum on the φ-ladder: two states
separated by an integer rung gap `k` (with the same yardstick and gap class)
stand in the exact dimensionless ratio `φ^k`. `φ` itself (T6) is the primitive
forced dimensionless ratio; every ladder gap is one of its integer powers.

This module makes that ratio *computable and certified without the continuum*:

1. `phiPow k = φ^k` as an explicit element of ℤ[φ] (structural recursion, so it
   reduces under both the kernel and the compiler — `#eval (phiPow 5)` prints
   `⟨3, 5⟩`, i.e. `3 + 5φ`, and `decide` reduces it the same way).
2. `RatLt p q x` / `RatGt p q x`: the decidable integer predicates "`p/q < x`"
   and "`x < p/q`" on ℤ[φ], defined by reusing the sigma0 sign predicate `IsPos`
   on the witness `q·x − p`. Because `IsPos` is decidable and choice-free, every
   concrete bracket closes by `decide` inside `{propext, Quot.sound}` and is
   independently confirmed by `#eval`.
3. Certified brackets for φ and the representative rungs φ⁵, φ⁸ (the octave),
   tight to the stated rational precision — e.g. `1618033/1000000 < φ < 1618034/1000000`.

The mechanism is exactly the √5-irrationality machinery already proved at sigma0
in `DeltaSpine.GoldenInt`: `p/q < a + bφ` reduces to a sign question about
`s + t√5` with `s, t ∈ ℤ`, decided by comparing `s²` with `5t²` (a tie is
impossible because √5 is irrational, `int_sq_eq_five_sq`). No `Real.sqrt`, no
`Float`, no `native_decide` (which would inject `ofReduceBool`, breaking sigma0).

The bridge showing these brackets are genuine bounds on the *real* ratio
`φ^k ∈ ℝ` is `DeltaSpine.GoldenIntReal` (sigma1 CHOICE): the ordering and the
arithmetic are forced at sigma0; only the evaluation into ℝ costs
`Classical.choice`.

**Verdict target: sigma0 DELTA_FORCED** — every theorem here closes within
`{propext, Quot.sound}`. Audit with `scripts/sigma_audit.py`.

Delta Forcing Spectrum program: `Delta_Forcing_Spectrum_20260626.tex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine
namespace GoldenInt

/-! ## The computable φ-power ladder -/

/-- `φ^n` as an explicit element of ℤ[φ], by structural recursion. Unlike
    `phiZpow` (which routes through the unit group and does not reduce under
    `decide`/`#eval`), this reduces cleanly in the kernel and the compiler:
    `phiPow n = ⟨F(n−1), F(n)⟩` where `F` is Fibonacci. -/
def phiPow : ℕ → GoldenInt
  | 0 => 1
  | (n + 1) => phiPow n * phi

@[simp] theorem phiPow_zero : phiPow 0 = 1 := rfl

@[simp] theorem phiPow_succ (n : ℕ) : phiPow (n + 1) = phiPow n * phi := rfl

theorem phiPow_one : phiPow 1 = phi := by decide

/-- `φ⁵ = 5φ + 3 = ⟨3, 5⟩` — kernel computation. -/
theorem phiPow_five : phiPow 5 = ⟨3, 5⟩ := by decide

/-- `φ⁸ = 21φ + 13 = ⟨13, 21⟩` (the octave rung) — kernel computation. -/
theorem phiPow_eight : phiPow 8 = ⟨13, 21⟩ := by decide

/-- The computable ladder agrees with the unit-group ladder of
    `DeltaSpine.CostUniqueness` on ℕ, so these brackets are statements about
    the same `φⁿ` that carries `traceZ`/`Jdouble` (the T5 node). -/
theorem phiPow_eq_phiZpow (n : ℕ) : phiPow n = phiZpow (n : ℤ) := by
  induction n with
  | zero =>
      have e : ((0 : ℕ) : ℤ) = 0 := by decide
      rw [phiPow_zero, e, phiZpow_zero]
  | succ k ih =>
      have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
      rw [phiPow_succ, ih, e, phiZpow_add, phiZpow_one]

/-! ## Decidable rational brackets on ℤ[φ]

`p/q < a + bφ` (for `q > 0`) iff `0 < q·(a+bφ) − p`, i.e. `IsPos ⟨q·a − p, q·b⟩`.
Reusing the sigma0 sign predicate keeps everything decidable and choice-free. -/

/-- The witness element `q·x − p ∈ ℤ[φ]` whose sign decides `p/q ⋚ x`. -/
def ratWitness (p q : ℤ) (x : GoldenInt) : GoldenInt := ⟨q * x.a - p, q * x.b⟩

/-- The rational `p/q` lies strictly below `x` (interpreted over the reals when
    `q > 0`). Decidable integer predicate: `0 < q·x − p`. -/
def RatLt (p q : ℤ) (x : GoldenInt) : Prop := IsPos (ratWitness p q x)

/-- The rational `p/q` lies strictly above `x` (interpreted over the reals when
    `q > 0`). Decidable integer predicate: `0 < p − q·x`. -/
def RatGt (p q : ℤ) (x : GoldenInt) : Prop := IsPos (ratWitness (-p) q (-x))

instance (p q : ℤ) (x : GoldenInt) : Decidable (RatLt p q x) := by
  unfold RatLt; infer_instance

instance (p q : ℤ) (x : GoldenInt) : Decidable (RatGt p q x) := by
  unfold RatGt; infer_instance

/-! ## Certified brackets

Each bracket is a sigma0 theorem (closed by kernel `decide`, hence in
`{propext, Quot.sound}`) and is independently confirmed by `#eval` (runtime). -/

/-- **φ, lower bracket**: `1.618033 < φ`. -/
theorem phi_lower : RatLt 1618033 1000000 phi := by decide

/-- **φ, upper bracket**: `φ < 1.618034`. -/
theorem phi_upper : RatGt 1618034 1000000 phi := by decide

/-- **φ⁵, lower bracket**: `11.09 < φ⁵` (`φ⁵ ≈ 11.0902`). -/
theorem phi5_lower : RatLt 1109 100 (phiPow 5) := by decide

/-- **φ⁵, upper bracket**: `φ⁵ < 11.10`. -/
theorem phi5_upper : RatGt 1110 100 (phiPow 5) := by decide

/-- **φ⁸, lower bracket**: `46.978 < φ⁸` (`φ⁸ ≈ 46.9787`, the octave rung). -/
theorem phi8_lower : RatLt 46978 1000 (phiPow 8) := by decide

/-- **φ⁸, upper bracket**: `φ⁸ < 46.979`. -/
theorem phi8_upper : RatGt 46979 1000 (phiPow 8) := by decide

/-- **Forced-ratio thread, delta-forced (sigma0)**: the primitive forced
    dimensionless ratio φ and the representative ladder rungs φ⁵, φ⁸ are each
    pinned inside an explicit rational interval, entirely by choice-free integer
    arithmetic on ℤ[φ]. Every conjunct closes by `decide`, so the whole bundle
    lives in `{propext, Quot.sound}`. The real-side reading of these brackets is
    `DeltaSpine.GoldenIntReal.ladder_ratio_real_brackets` (sigma1). -/
theorem ladder_ratio_brackets :
    (RatLt 1618033 1000000 phi ∧ RatGt 1618034 1000000 phi) ∧
    (RatLt 1109 100 (phiPow 5) ∧ RatGt 1110 100 (phiPow 5)) ∧
    (RatLt 46978 1000 (phiPow 8) ∧ RatGt 46979 1000 (phiPow 8)) := by
  refine ⟨⟨phi_lower, phi_upper⟩, ⟨phi5_lower, phi5_upper⟩, ⟨phi8_lower, phi8_upper⟩⟩

/-! ## Runtime certificates (`#eval`)

These evaluate the same decidable predicates through the compiler, so the
rational bounds are confirmed by two independent engines (kernel + runtime).
They print `true`; `phiPow` prints its exact `⟨a, b⟩ = a + bφ` value. -/

/-- info: true -/
#guard_msgs in
#eval decide (RatLt 1618033 1000000 phi)

/-- info: true -/
#guard_msgs in
#eval decide (RatGt 1618034 1000000 phi)

/-- info: true -/
#guard_msgs in
#eval decide (RatLt 1109 100 (phiPow 5))

/-- info: true -/
#guard_msgs in
#eval decide (RatGt 1110 100 (phiPow 5))

/-- info: true -/
#guard_msgs in
#eval decide (RatLt 46978 1000 (phiPow 8))

/-- info: true -/
#guard_msgs in
#eval decide (RatGt 46979 1000 (phiPow 8))

end GoldenInt
end DeltaSpine
end Foundation
end IndisputableMonolith
