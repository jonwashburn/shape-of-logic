import Mathlib

/-!
# Hodge as the vanishing of a canonical nonnegative mass defect

This module is the honest endpoint of the RS physical-corollary method applied
to rational Hodge. It reformulates the conjecture as the vanishing of a single,
canonically defined, provably **nonnegative** real number per class: the mass
defect against the Wirtinger calibration bound. It cleanly separates the half
that is unconditionally true (nonnegativity, the calibration inequality) from
the half that is the conjecture (achievement of the bound).

## The physical-corollary translation

Fix a smooth projective complex variety `(X, Ω)` (Kähler form `Ω`), complex
dimension `n`, codimension `p`, so cycles have real dimension `2(n-p)`. For a
rational `(p,p)` class `c`:

* `calBound c` := the topological calibration pairing
  `⟨[Ω^{n-p}/(n-p)!], c⟩`. It depends only on the cohomology class.
* `minMass c` := the infimum of mass over integral currents representing (a
  fixed multiple of) `c`. Achieved by Federer–Fleming compactness.

Wirtinger's inequality (the fundamental theorem of calibrations on a Kähler
manifold) says `Ω^{n-p}/(n-p)!` has comass one and calibrates complex
subvarieties, hence `calBound c ≤ minMass c` for every class. The **mass
defect** is

    defect c := minMass c - calBound c ≥ 0.

The ledger reading (CPM / `J`-cost): `defect` is the unrecovered cost of the
mass-minimizer relative to the calibrated (complex-analytic) lower bound. It is
the exact nonnegative defect the Coercive Projection Method is built to track.

## What is proved here vs. what is the conjecture

* `defect_nonneg` (**unconditional**, given the named Wirtinger hypothesis): the
  defect is `≥ 0`. This is the genuinely true half. It is the calibration
  inequality, no more.
* `defect_eq_zero_iff_algebraic` (**characterization**, via two named classical
  bridges): the defect vanishes exactly on algebraic classes. The hard direction
  (`calibrated_is_algebraic`, defect-zero ⇒ algebraic) is Federer–Fleming
  achievement + the equality case of Wirtinger (calibrated ⇒ complex analytic) +
  Harvey–Shiffman + Chow. The easy direction (`algebraic_achieves_bound`) is
  that the Kähler form calibrates an algebraic cycle, so it meets the bound.
* `hodge_iff_defect_vanishes`: rational Hodge holds iff the defect vanishes on
  every class.

## Honest status

This is a **reformulation**, not a proof. Its value over the bare circularity
guard (`HodgeIntegralCurrentCircularity`) is that it isolates the unconditional
content (`defect_nonneg`) from the conjectural content (defect `= 0`), and names
the conjecture as the vanishing of one canonical nonnegative functional. Per
`rs-physical-corollary-math.mdc`, this is the "named missing lemma" the method
is supposed to produce: **the mass defect of every rational `(p,p)` class
vanishes.** No RS theorem in the library forces that vanishing; doing so would
prove Hodge. The integral Atiyah–Hirzebruch counterexamples are exactly classes
whose integral defect stays positive; the rational question is whether the
amortized defect `defect(m·c)/m → 0` for all rational Hodge `c`, which is open.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeMassDefectReformulation

universe u

variable {Class : Type u}

/-- The mass defect against the calibration bound. -/
def defect (minMass calBound : Class → ℝ) (c : Class) : ℝ :=
  minMass c - calBound c

/-- **Unconditional half (Wirtinger calibration inequality).** Given that the
topological calibration bound lower-bounds the mass of any representative, the
mass defect is nonnegative. This is the genuinely true content; it is the
calibration inequality and nothing more. -/
theorem defect_nonneg
    {minMass calBound : Class → ℝ}
    (wirtinger : ∀ c, calBound c ≤ minMass c) (c : Class) :
    0 ≤ defect minMass calBound c := by
  have h := wirtinger c
  unfold defect
  linarith

/-- The defect is zero exactly when the mass-minimizer meets the calibration
bound. -/
theorem defect_eq_zero_iff_mass_eq_bound
    (minMass calBound : Class → ℝ) (c : Class) :
    defect minMass calBound c = 0 ↔ minMass c = calBound c := by
  unfold defect
  exact sub_eq_zero

/-- **Characterization half (Hodge-equivalent).** The mass defect vanishes
exactly on algebraic classes. The hard direction is Federer–Fleming achievement
plus the Wirtinger equality case plus Harvey–Shiffman plus Chow
(`calibrated_is_algebraic`); the easy direction is that the Kähler form
calibrates an algebraic cycle (`algebraic_achieves_bound`). -/
theorem defect_eq_zero_iff_algebraic
    {minMass calBound : Class → ℝ} {algebraic : Class → Prop}
    (calibrated_is_algebraic : ∀ c, minMass c = calBound c → algebraic c)
    (algebraic_achieves_bound : ∀ c, algebraic c → minMass c = calBound c)
    (c : Class) :
    defect minMass calBound c = 0 ↔ algebraic c := by
  rw [defect_eq_zero_iff_mass_eq_bound]
  exact ⟨calibrated_is_algebraic c, algebraic_achieves_bound c⟩

/-- **Rational Hodge as defect vanishing.** Rational Hodge (every class is
algebraic) holds iff the canonical nonnegative mass defect vanishes on every
class. The single open lemma is the right-hand side. -/
theorem hodge_iff_defect_vanishes
    {minMass calBound : Class → ℝ} {algebraic : Class → Prop}
    (calibrated_is_algebraic : ∀ c, minMass c = calBound c → algebraic c)
    (algebraic_achieves_bound : ∀ c, algebraic c → minMass c = calBound c) :
    (∀ c, algebraic c) ↔ (∀ c, defect minMass calBound c = 0) :=
  ⟨fun h c =>
      (defect_eq_zero_iff_algebraic calibrated_is_algebraic algebraic_achieves_bound c).mpr (h c),
   fun h c =>
      (defect_eq_zero_iff_algebraic calibrated_is_algebraic algebraic_achieves_bound c).mp (h c)⟩

/-- The defect functional packaged with its unconditional lower bound and its
characterization. This is the honest object: a nonnegative real per class whose
vanishing is the conjecture. -/
structure MassDefectLedger (Class : Type u) where
  minMass : Class → ℝ
  calBound : Class → ℝ
  algebraic : Class → Prop
  /-- Wirtinger calibration inequality: unconditional. -/
  wirtinger : ∀ c, calBound c ≤ minMass c
  /-- Federer–Fleming + Wirtinger equality + Harvey–Shiffman + Chow. -/
  calibrated_is_algebraic : ∀ c, minMass c = calBound c → algebraic c
  /-- Kähler form calibrates an algebraic cycle. -/
  algebraic_achieves_bound : ∀ c, algebraic c → minMass c = calBound c

namespace MassDefectLedger

/-- The defect of a class in the ledger. -/
def defectAt (L : MassDefectLedger Class) (c : Class) : ℝ :=
  defect L.minMass L.calBound c

/-- The ledger defect is unconditionally nonnegative. -/
theorem defectAt_nonneg (L : MassDefectLedger Class) (c : Class) :
    0 ≤ L.defectAt c :=
  defect_nonneg L.wirtinger c

/-- The ledger defect vanishes exactly on algebraic classes. -/
theorem defectAt_eq_zero_iff_algebraic (L : MassDefectLedger Class) (c : Class) :
    L.defectAt c = 0 ↔ L.algebraic c :=
  defect_eq_zero_iff_algebraic L.calibrated_is_algebraic L.algebraic_achieves_bound c

/-- Rational Hodge for the ledger is the vanishing of the nonnegative defect. -/
theorem hodge_iff_defect_vanishes (L : MassDefectLedger Class) :
    (∀ c, L.algebraic c) ↔ (∀ c, L.defectAt c = 0) :=
  HodgeMassDefectReformulation.hodge_iff_defect_vanishes
    L.calibrated_is_algebraic L.algebraic_achieves_bound

end MassDefectLedger

end HodgeMassDefectReformulation
end Mathematics
end IndisputableMonolith
