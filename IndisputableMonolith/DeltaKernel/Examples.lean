import IndisputableMonolith.DeltaKernel.Syntax
import IndisputableMonolith.DeltaKernel.Ledger
import IndisputableMonolith.DeltaKernel.Check
import IndisputableMonolith.DeltaKernel.Semantics
import IndisputableMonolith.DeltaKernel.Sound

/-!
# δ-Kernel: Worked Examples

Concrete derivation trees checked by the kernel, demonstrating each verdict
class end to end:

1. `one_plus_one`: a FORCED equational proof of `1 + 1 = 2` from the
   recursion equations (no induction, no posits).
2. `zeroAdd`: a FORCED induction proof of `∀x, 0 + x = x` at the
   QF-induction tier, then EXPORTED through `sound_forced` to a host
   theorem about `Nat` whose axiom closure is choice-free. This is the
   full pipeline: δ-derivation → kernel audit → canonical-model truth.
3. `fullIndDemo`: induction on a quantified formula. The kernel accepts it
   and posts the `indFull` TIER flag: `FORCED @ FULL-IND`, distinguished
   from example 2's `FORCED @ QF-IND`.
4. EM contrast: the SAME decidable disjunction `0 = 0 ∨ ¬(0 = 0)` obtained
   two ways: via the EM posit (ledger posts `em`) and via `disjIntro1` on
   `eqRefl` (ledger empty). The ledger measures that the schematic posit
   was never needed for the concrete instance.
5. MP guard: the Markov posit accepts a quantifier-free matrix and REJECTS
   a quantified one. The guard is the checker itself, not a convention.

Everything here is verified by `decide`/`rfl` against the executable
checker: the kernel, not the host's proof search, is what accepts these
trees. No Mathlib.
-/

namespace IndisputableMonolith
namespace DeltaKernel
namespace Examples

open DTerm DFormula

/-! ## Numerals -/

/-- `1` as a δ-term: one distinction step. -/
def one : DTerm := .succ .zero

/-- `2` as a δ-term: two distinction steps. -/
def two : DTerm := .succ (.succ .zero)

/-! ## Example 1: `1 + 1 = 2`, FORCED, no induction

Chain: `addSucc` gives `1 + S0 = S(1 + 0)`; `addZero` gives `1 + 0 = 1`;
Leibniz substitution into the hole `1 + S0 = S(x₀)` rewrites `1 + 0` to `1`
on the right, landing `1 + 1 = S1 = 2`. -/

/-- Derivation of `1 + 1 = 2`. The hole formula's `var 0` marks the position
being rewritten by `eqSubst`. -/
def onePlusOne : Deriv :=
  .eqSubst (.eq (.add one (.succ .zero)) (.succ (.var 0)))
    (.add one .zero)   -- t : the term being replaced
    one                -- s : its equal
    (.addZero one)     -- ⊢ 1 + 0 = 1
    (.addSucc one .zero)  -- ⊢ 1 + S0 = S(1 + 0), the hole at t

/-- The kernel accepts `onePlusOne` with the EMPTY ledger: σ0 / DELTA_FORCED. -/
theorem onePlusOne_forced :
    check [] onePlusOne = some (.eq (.add one one) two, .empty) := by
  decide

/-- Exported to the host: `1 + 1 = 2` in `Nat`, certified through the
δ-kernel and the canonical model rather than by host arithmetic. -/
theorem one_plus_one_certified : 1 + 1 = 2 :=
  sound_forced onePlusOne_forced (fun _ => 0)

/-! ## Example 2: `∀x, 0 + x = x` by QF induction, FORCED, exported

The induction formula `0 + x₀ = x₀` is quantifier-free, so the induction
rule stays in the QF tier and the ledger remains empty: the theorem is
FORCED @ QF-IND, the strongest verdict the kernel issues. -/

/-- The induction formula: `0 + x₀ = x₀`. -/
def zeroAddFormula : DFormula := .eq (.add .zero (.var 0)) (.var 0)

/-- The Leibniz hole for the induction step. Written one binder in (inside
`eqSubst`'s substitution), so the ambient induction variable is `var 1`
and the rewrite position is `var 0`:
`0 + S(x₁) = S(x₀)`. Substituting `t = 0 + x₀` gives the `addSucc` axiom
instance; substituting `s = x₀` gives the step goal. -/
def zeroAddHole : DFormula := .eq (.add .zero (.succ (.var 1))) (.succ (.var 0))

/-- The induction step: `∀x (0 + x = x → 0 + Sx = Sx)`. Under the hypothesis
(de Bruijn `hyp 0`), rewrite `0 + x` to `x` inside `0 + Sx = S(0 + x)`. -/
def zeroAddStep : Deriv :=
  .allIntro (.implIntro zeroAddFormula
    (.eqSubst zeroAddHole (.add .zero (.var 0)) (.var 0)
      (.hyp 0)
      (.addSucc .zero (.var 0))))

/-- The full induction derivation for `∀x, 0 + x = x`. -/
def zeroAdd : Deriv := .ind zeroAddFormula (.addZero .zero) zeroAddStep

/-- The kernel accepts `zeroAdd` with the EMPTY ledger: no posits, and the
QF tier (the induction formula is quantifier-free, so `indFull` stays
`false`). FORCED @ QF-IND. -/
theorem zeroAdd_forced :
    check [] zeroAdd = some (.all zeroAddFormula, .empty) := by
  decide

/-- Exported to the host: `∀ n, 0 + n = n` over `Nat`, certified through the
δ-kernel. The proof term routes through `sound_forced`, so its axiom
closure is choice-free; `#print axioms` below is the audit. -/
theorem zero_add_certified (n : Nat) : 0 + n = n :=
  sound_forced zeroAdd_forced (fun _ => 0) n

/-! ## Example 3: the FULL-IND tier flag

Induction on `∀y (y = y)`: the formula has a quantifier, so `isQF` is
`false` and the kernel posts the `indFull` tier marker. Still no posits:
the verdict is FORCED @ FULL-IND. The base and step are trivial because
`(∀y, y = y).stepSucc` computes back to `∀y, y = y` (the induction variable
does not occur), which is exactly what makes this a minimal tier demo. -/

/-- A quantified induction formula: `∀y, y = y` (the outer induction
variable `x₀` does not occur; only its quantifier structure matters). -/
def quantFormula : DFormula := .all (.eq (.var 0) (.var 0))

/-- Induction over a quantified formula. Base: `∀y, y = y` by `eqRefl`.
Step: the implication is the identity since `stepSucc` fixes the formula. -/
def fullIndDemo : Deriv :=
  .ind quantFormula
    (.allIntro (.eqRefl (.var 0)))
    (.allIntro (.implIntro quantFormula (.hyp 0)))

/-- The kernel accepts `fullIndDemo` and posts the TIER flag: ledger
`ofIndFull` = no posits, full-induction tier. FORCED @ FULL-IND. -/
theorem fullIndDemo_tier :
    check [] fullIndDemo = some (.all quantFormula, .ofIndFull) := by
  decide

/-! ## Example 4: EM measured, not assumed

The disjunction `0 = 0 ∨ ¬(0 = 0)` two ways. The posit route consumes EM
schematically; the direct route proves the left disjunct and pays nothing.
The ledger difference IS the measurement: for this decidable instance the
classical posit was noise. -/

/-- `0 = 0`, the atom for the EM contrast. -/
def zeroEq : DFormula := .eq .zero .zero

/-- Route A: the EM posit. -/
def emRoute : Deriv := .emPosit zeroEq

/-- Route B: prove the left disjunct directly. -/
def forcedRoute : Deriv := .disjIntro1 zeroEq.neg (.eqRefl .zero)

/-- Route A posts `em`: the verdict is CONDITIONAL {EM}. -/
theorem emRoute_posts_em :
    check [] emRoute = some (.disj zeroEq zeroEq.neg, .ofEM) := by
  decide

/-- Route B proves the SAME formula with the EMPTY ledger: FORCED. -/
theorem forcedRoute_forced :
    check [] forcedRoute = some (.disj zeroEq zeroEq.neg, .empty) := by
  decide

/-! ## Example 5: the Markov guard is the checker

`mpPosit` demands a quantifier-free matrix. A QF matrix is accepted (posting
`mp`); a quantified matrix is REJECTED: `check` returns `none`. There is no
way to smuggle a strong Markov principle past the ledger. -/

/-- A quantifier-free matrix: `x₀ = 0`. -/
def qfMatrix : DFormula := .eq (.var 0) .zero

/-- Markov on a QF matrix: accepted, posts `mp`. -/
theorem mp_accepts_qf :
    check [] (.mpPosit qfMatrix) =
      some (.impl (.neg (.neg (.ex qfMatrix))) (.ex qfMatrix), .ofMP) := by
  decide

/-- Markov on a quantified matrix: REJECTED by the kernel (not merely
discouraged). -/
theorem mp_rejects_quantified :
    check [] (.mpPosit (.all (.eq (.var 0) (.var 0)))) = none := by
  decide

/-! ## Axiom audits

The exported host theorems certified through FORCED derivations must be
choice-free: their closures may contain `propext` and `Quot.sound` (host
metatheory plumbing) but never `Classical.choice`. This is the kernel's
σ-ledger agreeing with Lean's own axiom tracker. -/

#print axioms one_plus_one_certified

#print axioms zero_add_certified

end Examples
end DeltaKernel
end IndisputableMonolith
