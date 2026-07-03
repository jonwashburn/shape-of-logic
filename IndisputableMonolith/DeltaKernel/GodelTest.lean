import IndisputableMonolith.DeltaKernel.Syntax
import IndisputableMonolith.DeltaKernel.Ledger
import IndisputableMonolith.DeltaKernel.Check
import IndisputableMonolith.DeltaKernel.Semantics
import IndisputableMonolith.DeltaKernel.Sound
import IndisputableMonolith.DeltaKernel.Sigma
import IndisputableMonolith.DeltaKernel.Examples

/-!
# δ-Kernel: The Gödel Test (Pre-Registered Pricing Battery)

The pre-registered question: does the σ-ledger PRICE derivations, or merely
decorate them? The test: take ONE fixed theorem and derive it along TWO
genuinely different routes, then read the ledgers.

Target: commutativity of distinction-composition, `∀x ∀y, x + y = y + x`,
the first theorem of arithmetic whose textbook proof reaches for induction
twice.

- **Route 1 (careful):** every induction formula is quantifier-free.
  `succAdd` (`∀x∀y, Sx + y = S(x+y)`) by QF induction on `y`, then
  `addComm` by QF induction on `y` with `x` held free by an outer
  generalization. PREDICTED verdict: `FORCED @ QF-IND`, ledger empty.
- **Route 2 (convenient):** the textbook shortcut, induction on `x` with
  the QUANTIFIED induction formula `∀y, x + y = y + x`. The step gets to
  instantiate its hypothesis at any `y` it likes, which is exactly the
  convenience full induction buys. PREDICTED verdict: `FORCED @ FULL-IND`,
  ledger posts the `indFull` tier flag.

Both predictions are checked below by `decide` against the executable
kernel, and re-checked by the SYNTACTIC scans of `Sigma.lean`
(`positFree` / `usesFullInd`), so the pricing is grep-auditable. Both
routes then EXPORT through soundness to the same host theorem with a
choice-free axiom closure: the tier flag measures PROOF-ROUTE strength,
never truth.

Honest scope: this is the pricing half of the Gödel program. The full
arithmetization (encoding `Deriv` inside ℕδ and deriving the kernel's own
soundness at a measured tier) is OPEN and pre-registered as future work;
Cantor pairing over the distinction signature is the intended sequence
encoding. Nothing here claims it.

Everything verified by `decide` against the executable checker. No Mathlib.
-/

namespace IndisputableMonolith
namespace DeltaKernel
namespace GodelTest

open DTerm DFormula Examples

/-! ## Equational combinators

Three closed combinators over `Deriv`, each a single `eqSubst` with the
hole chosen so the checker computes the intended conclusion. They build
TREES; the kernel still audits every use (nothing here bypasses `check`). -/

/-- Symmetry: from a derivation of `t = s`, build one of `s = t`.
Hole `x₀ = t↑`: at `t` it is `t = t` (refl), at `s` it is `s = t`. -/
def dSymm (t s : DTerm) (d : Deriv) : Deriv :=
  .eqSubst (.eq (.var 0) (t.lift 1 0)) t s d (.eqRefl t)

/-- Transitivity: from derivations of `s = r` and `t = s`, build `t = r`.
Hole `t↑ = x₀`: at `s` it is `t = s` (the second premise), at `r` it is
`t = r`. -/
def dTrans (t s r : DTerm) (dsr dts : Deriv) : Deriv :=
  .eqSubst (.eq (t.lift 1 0) (.var 0)) s r dsr dts

/-- Successor congruence: from a derivation of `t = s`, build `S t = S s`.
Hole `S t↑ = S x₀`: at `t` it is `S t = S t` (refl), at `s` it is
`S t = S s`. -/
def dSuccCong (t s : DTerm) (d : Deriv) : Deriv :=
  .eqSubst (.eq (.succ (t.lift 1 0)) (.succ (.var 0))) t s d (.eqRefl (.succ t))

/-! ## Route 1, lemma: `∀x ∀y, S x + y = S (x + y)` at QF-IND

Induction on `y` (de Bruijn 0) with `x` free (de Bruijn 1), generalized by
an outer `allIntro`. The induction formula is quantifier-free. -/

/-- The QF induction formula: `S x₁ + x₀ = S (x₁ + x₀)`. -/
def succAddFormula : DFormula :=
  .eq (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0)))

/-- Base: `S x + 0 = S (x + 0)`. Chain `S x + 0 = S x = S (x + 0)` through
`addZero` twice, symmetry, and successor congruence. -/
def succAddBase : Deriv :=
  dTrans (.add (.succ (.var 0)) .zero) (.succ (.var 0)) (.succ (.add (.var 0) .zero))
    (dSuccCong (.var 0) (.add (.var 0) .zero)
      (dSymm (.add (.var 0) .zero) (.var 0) (.addZero (.var 0))))
    (.addZero (.succ (.var 0)))

/-- Step body, under hypothesis `S x + y = S (x + y)` (hyp 0):
`S x + S y = S (S x + y) = S (S (x + y)) = S (x + S y)`. -/
def succAddStepBody : Deriv :=
  dTrans (.add (.succ (.var 1)) (.succ (.var 0)))
    (.succ (.succ (.add (.var 1) (.var 0))))
    (.succ (.add (.var 1) (.succ (.var 0))))
    (dSuccCong (.succ (.add (.var 1) (.var 0))) (.add (.var 1) (.succ (.var 0)))
      (dSymm (.add (.var 1) (.succ (.var 0))) (.succ (.add (.var 1) (.var 0)))
        (.addSucc (.var 1) (.var 0))))
    (dTrans (.add (.succ (.var 1)) (.succ (.var 0)))
      (.succ (.add (.succ (.var 1)) (.var 0)))
      (.succ (.succ (.add (.var 1) (.var 0))))
      (dSuccCong (.add (.succ (.var 1)) (.var 0)) (.succ (.add (.var 1) (.var 0)))
        (.hyp 0))
      (.addSucc (.succ (.var 1)) (.var 0)))

/-- `∀x ∀y, S x + y = S (x + y)` by QF induction on `y`. -/
def succAdd : Deriv :=
  .allIntro (.ind succAddFormula succAddBase
    (.allIntro (.implIntro succAddFormula succAddStepBody)))

/-- The kernel accepts `succAdd` with the EMPTY ledger: FORCED @ QF-IND. -/
theorem succAdd_forced :
    check [] succAdd = some (.all (.all succAddFormula), .empty) := by
  decide

/-! ## Route 1: `∀x ∀y, x + y = y + x` at QF-IND -/

/-- The commutativity matrix: `x₁ + x₀ = x₀ + x₁` (quantifier-free). -/
def commFormula : DFormula :=
  .eq (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1))

/-- Base: `x + 0 = 0 + x`. Chain `x + 0 = x = 0 + x` through `addZero`,
`zeroAdd` (Example 2's QF-IND theorem, reused as a sub-tree), symmetry. -/
def addCommBase : Deriv :=
  dTrans (.add (.var 0) .zero) (.var 0) (.add .zero (.var 0))
    (dSymm (.add .zero (.var 0)) (.var 0) (.allElim (.var 0) zeroAdd))
    (.addZero (.var 0))

/-- Step body, under hypothesis `x + y = y + x` (hyp 0):
`x + S y = S (x + y) = S (y + x) = S y + x`, the last leg through
`succAdd` instantiated at `(y, x)`. -/
def addCommStepBody : Deriv :=
  dTrans (.add (.var 1) (.succ (.var 0)))
    (.succ (.add (.var 0) (.var 1)))
    (.add (.succ (.var 0)) (.var 1))
    (dSymm (.add (.succ (.var 0)) (.var 1)) (.succ (.add (.var 0) (.var 1)))
      (.allElim (.var 1) (.allElim (.var 0) succAdd)))
    (dTrans (.add (.var 1) (.succ (.var 0)))
      (.succ (.add (.var 1) (.var 0)))
      (.succ (.add (.var 0) (.var 1)))
      (dSuccCong (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1)) (.hyp 0))
      (.addSucc (.var 1) (.var 0)))

/-- Route 1: `∀x ∀y, x + y = y + x`, every induction formula QF. -/
def addComm : Deriv :=
  .allIntro (.ind commFormula addCommBase
    (.allIntro (.implIntro commFormula addCommStepBody)))

/-- ROUTE 1 VERDICT (pre-registered): the careful route is accepted with
the EMPTY ledger. `FORCED @ QF-IND`, the strongest verdict the kernel
issues, for full commutativity of addition. -/
theorem addComm_forced :
    check [] addComm = some (.all (.all commFormula), .empty) := by
  decide

/-! ## Route 2: the same theorem through FULL induction

Induction on `x` with the QUANTIFIED formula `∀y, x + y = y + x`. The step
instantiates its induction hypothesis at the bound `y`, which is the
convenience that only a non-QF induction formula provides. -/

/-- The quantified induction formula: `∀y, x₀ + y = y + x₀` (as a formula
in the induction variable, `.all commFormula`). NOT quantifier-free. -/
def commAllFormula : DFormula := .all commFormula

/-- Base: `∀y, 0 + y = y + 0`. Chain `0 + y = y = y + 0`. -/
def addCommFullBase : Deriv :=
  .allIntro
    (dTrans (.add .zero (.var 0)) (.var 0) (.add (.var 0) .zero)
      (dSymm (.add (.var 0) .zero) (.var 0) (.addZero (.var 0)))
      (.allElim (.var 0) zeroAdd))

/-- Step inner body, under hypothesis `∀y, x + y = y + x` (hyp 0, lifted):
`S x + y = S (x + y) = S (y + x) = y + S x`, the middle leg by
INSTANTIATING the quantified hypothesis at `y`. -/
def addCommFullStepBody : Deriv :=
  dTrans (.add (.succ (.var 1)) (.var 0))
    (.succ (.add (.var 0) (.var 1)))
    (.add (.var 0) (.succ (.var 1)))
    (dSymm (.add (.var 0) (.succ (.var 1))) (.succ (.add (.var 0) (.var 1)))
      (.addSucc (.var 0) (.var 1)))
    (dTrans (.add (.succ (.var 1)) (.var 0))
      (.succ (.add (.var 1) (.var 0)))
      (.succ (.add (.var 0) (.var 1)))
      (dSuccCong (.add (.var 1) (.var 0)) (.add (.var 0) (.var 1))
        (.allElim (.var 0) (.hyp 0)))
      (.allElim (.var 0) (.allElim (.var 1) succAdd)))

/-- Route 2: the SAME statement `∀x ∀y, x + y = y + x` by induction on the
quantified formula. -/
def addCommFull : Deriv :=
  .ind commAllFormula addCommFullBase
    (.allIntro (.implIntro commAllFormula (.allIntro addCommFullStepBody)))

/-- ROUTE 2 VERDICT (pre-registered): the convenient route proves the SAME
formula but the ledger posts the TIER flag: `FORCED @ FULL-IND`. The
kernel priced the shortcut. -/
theorem addCommFull_tier :
    check [] addCommFull = some (.all (.all commFormula), .ofIndFull) := by
  decide

/-! ## The pricing verdict, stated as one theorem

Same conclusion, different price. This is the Gödel-test discrimination
the panel pre-registered: the ledger is a measurement of the derivation
ROUTE, not a function of the theorem statement. -/

theorem pricing_discriminates :
    (check [] addComm = some (.all (.all commFormula), .empty)) ∧
    (check [] addCommFull = some (.all (.all commFormula), .ofIndFull)) :=
  ⟨addComm_forced, addCommFull_tier⟩

/-! ## The syntactic cross-audit (oracle symbols)

The same verdicts read off by the grep-level scans of `Sigma.lean`,
independent of the checker: both trees are posit-free; only Route 2
contains a FULL-IND symbol. -/

theorem addComm_syntactic_audit :
    positFree addComm = true ∧ usesFullInd addComm = false := by
  decide

theorem addCommFull_syntactic_audit :
    positFree addCommFull = true ∧ usesFullInd addCommFull = true := by
  decide

/-! ## Export: both routes certify the same host theorem, choice-free

The tier flag prices the route; it does not gate truth. Route 1 exports
through `sound_forced`. Route 2's ledger posts no POSIT (only the tier
flag), so its gates are also discharged vacuously and the export is
equally choice-free. `#print axioms` below is the audit. -/

/-- Commutativity of `Nat` addition, certified through the δ-kernel's
CAREFUL route (`FORCED @ QF-IND`). -/
theorem add_comm_certified (n m : Nat) : n + m = m + n :=
  sound_forced addComm_forced (fun _ => 0) n m

/-- The tier-only ledger gates nothing: `ofIndFull` posts no posit, so all
three metatheoretic gates are discharged vacuously, exactly as for the
empty ledger. -/
theorem Gated.ofIndFull : Gated Ledger.ofIndFull :=
  ⟨fun h => by simp [Ledger.ofIndFull] at h,
   fun h => by simp [Ledger.ofIndFull] at h,
   fun h => by simp [Ledger.ofIndFull] at h⟩

/-- Commutativity of `Nat` addition, certified through the δ-kernel's
CONVENIENT route (`FORCED @ FULL-IND`). Still choice-free: the tier flag
measures proof-route strength, not metatheoretic consumption. -/
theorem add_comm_full_certified (n m : Nat) : n + m = m + n := by
  have h := sound_cond addCommFull [] (.all (.all commFormula)) Ledger.ofIndFull
    addCommFull_tier Gated.ofIndFull (fun _ => 0) (fun ψ hψ => by cases hψ)
  exact h n m

/-! ## Axiom audits

Both exports must be choice-free (no `Classical.choice`): the kernel's
σ-ledger agreeing with Lean's own axiom tracker on both routes. -/

#print axioms add_comm_certified

#print axioms add_comm_full_certified

end GodelTest
end DeltaKernel
end IndisputableMonolith
