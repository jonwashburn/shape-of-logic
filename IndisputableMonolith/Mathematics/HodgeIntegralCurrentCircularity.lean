import Mathlib

/-!
# Integral-`(p,p)`-current target is Hodge-equivalent (RED-FLAG CIRCULARITY GUARD)

This module records, as a Lean theorem, the truth about the "integrality of the
CPT/energy-minimal current" target: it is **logically equivalent to the rational
Hodge conjecture itself**, class by class. It is therefore not a strictly weaker
lemma, and any "proof" of it that does not introduce genuinely new
algebraic-geometric input is circular.

## Why this is the honest verdict

Fix a smooth projective complex variety `X` and a codimension `p`. Let `c` range
over the rational `(p,p)` Hodge classes. Consider two predicates on `c`:

* `algebraic c` : `c` is a ℚ-linear combination of classes of algebraic cycles
  (this is the rational Hodge conjecture, asserted classwise).
* `integralPP c` : `c` is represented by a closed integral rectifiable `(p,p)`
  current.

There are exactly two bridges between them, and both are real classical
theorems already isolated in the project:

* **Forward (trivial):** an algebraic cycle is a closed integral `(p,p)` current
  (integration over the subvariety with integer multiplicities). So
  `algebraic c → integralPP c`.
* **Backward (Harvey–Shiffman + Chow):** a closed integral `(p,p)` current is a
  holomorphic chain (Harvey–Shiffman), and a projective analytic cycle is
  algebraic (Chow). So `integralPP c → algebraic c`. This is exactly
  `HodgeKingChowBridge.algebraic_cycle_from_closed_integral_pp_current`
  applied through `HarveyShiffmanTheoremShape` and `ProjectiveChowTheoremShape`.

Composing the two bridges gives `integralPP c ↔ algebraic c` for every `c`.
Hence "every rational `(p,p)` class has a closed integral `(p,p)` current
representative" is *the same statement* as the rational Hodge conjecture. This
is the currents-route analogue of the 2026-05-26 "Moment Surjectivity is
Hodge-equivalent" finding recorded in `HodgeCoreClosureStatus`.

## Why CPT / energy minimization cannot supply the missing direction

The backward bridge needs the current to be simultaneously **integral** and of
**type `(p,p)`**. Energy (`L²` / `J`-cost) minimization over currents in a fixed
rational `(p,p)` class lands on the *harmonic* representative, which is a
*smooth* `(p,p)` form, not an integral current. Minimizing mass over *integral*
currents in a real homology class (Federer–Fleming) does produce an integral
current, but the `(p,p)` projection `π^{p,p}` of an integral current is in
general a non-integral complex combination: `π^{p,p}` destroys integrality.
The conjunction "integral ∧ `(p,p)`" is precisely what Hodge asserts can be
achieved, and no energy/mass functional forces it. So the CPT-minimizer target
is not a tractable sub-lemma; it is the conjecture in currents costume.

The integral Hodge conjecture is moreover *false* (Atiyah–Hirzebruch, Kollár):
torsion / Steenrod obstructions block integral `(p,p)` classes from being
algebraic. The rational version clears denominators and so escapes those torsion
counterexamples, but the integral-`(p,p)` conjunction above is exactly the
residue that remains open.

## Status

This module is a **guard**, not a result. The theorems below are logically
shallow (they compose two supplied bridges); their value is to make the
circularity a checked artifact so future work cannot relaunder the integral
current target as if it were weaker than Hodge.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeIntegralCurrentCircularity

universe u

variable {Class : Type u}

/-- **Per-class circularity.** Given the trivial forward bridge
(`algebraic → integral (p,p) current`) and the backward Harvey–Shiffman + Chow
bridge (`integral (p,p) current → algebraic`), the integral-`(p,p)`-current
predicate is *equivalent* to algebraicity for every class. The currents target
carries no content beyond rational Hodge. -/
theorem integralPP_iff_algebraic
    {algebraic integralPP : Class → Prop}
    (cycle_to_current : ∀ c, algebraic c → integralPP c)
    (harveyShiffman_chow : ∀ c, integralPP c → algebraic c)
    (c : Class) :
    integralPP c ↔ algebraic c :=
  ⟨harveyShiffman_chow c, cycle_to_current c⟩

/-- **Quantified circularity.** "Every rational `(p,p)` class has a closed
integral `(p,p)` current representative" is logically equivalent to the rational
Hodge conjecture (asserted classwise). The integral-current target is Hodge, not
a weaker lemma. -/
theorem hodge_iff_integral_pp_target
    {algebraic integralPP : Class → Prop}
    (cycle_to_current : ∀ c, algebraic c → integralPP c)
    (harveyShiffman_chow : ∀ c, integralPP c → algebraic c) :
    (∀ c, integralPP c) ↔ (∀ c, algebraic c) :=
  ⟨fun h c => harveyShiffman_chow c (h c),
   fun h c => cycle_to_current c (h c)⟩

/-- **No free lunch.** If a route proves the integral-`(p,p)`-current target
using only the forward (trivial) bridge as its sole input about algebraicity,
then it has proved rational Hodge outright. Stated contrapositively: a genuine
proof of the target must introduce algebraic-geometric content strictly beyond
"algebraic cycles are integral currents." -/
theorem integral_pp_target_forces_hodge
    {algebraic integralPP : Class → Prop}
    (harveyShiffman_chow : ∀ c, integralPP c → algebraic c)
    (target : ∀ c, integralPP c) :
    ∀ c, algebraic c :=
  fun c => harveyShiffman_chow c (target c)

end HodgeIntegralCurrentCircularity
end Mathematics
end IndisputableMonolith
