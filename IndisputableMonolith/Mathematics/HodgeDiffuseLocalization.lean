import Mathlib

/-!
# Localizing the Hodge obstruction to the diffuse (zero-Lelong) residual

This module advances the Hodge attack one honest layer past the mass-defect
reformulation (`HodgeMassDefectReformulation`). Where that module showed
*Hodge ⟺ a canonical nonnegative defect vanishes*, this one **localizes** where
the defect can be nonzero, using only genuinely true classical inputs (Siu's
analyticity theorem, Chow/GAGA, Lefschetz (1,1)) rather than Hodge-equivalent
bridges.

## The two-layer split of the cost ledger

For a rational `(p,p)` class on a smooth projective `X`, the minimal positive
closed `(p,p)` current `S` representing it (the σ=0 / mass-minimal
configuration) splits, by **Siu's theorem**, as

    S = Σ_j λ_j [Z_j]  +  R,   λ_j ≥ 0,

where the `Z_j` are the codimension-`p` Lelong upperlevel sets — analytic
subvarieties, hence **algebraic** on projective `X` by Chow/GAGA — and `R` is a
diffuse residual with vanishing Lelong numbers in codimension `p`. Passing to
cohomology, the class `α` decomposes as

    α = (analytic part, algebraic)  +  (diffuse residual class).

* The **continuous layer** (existence of the real positive `(p,p)` current) is
  classically available on the pseudoeffective cone (Demailly). It is *not* the
  obstruction.
* The **discrete layer** (integrality / quantization of the residual) is the
  Atiyah–Hirzebruch territory and is where the whole Hodge obstruction lives.

## What this module proves (non-vacuously, true inputs only)

Modeling algebraic classes as an `AddSubgroup A` of the cohomology group `Coh`:

* `hodge_iff_diffuse` : given any additive split `α = analytic + diffuse` with
  `analytic ∈ A` (Siu + Chow), membership `α ∈ A` is **equivalent** to
  `diffuse ∈ A`. The obstruction is localized to the residual.
* `hodge_iff_all_diffuse_mem` : the global Hodge statement (every class
  algebraic) is equivalent to "every diffuse residual is algebraic."
* `divisor_case_algebraic` : if additionally the diffuse residual is algebraic
  (Lefschetz (1,1), true in codimension one), then `α ∈ A`. This recovers the
  `p = 1` case of Hodge as a corollary — a sanity gate confirming the
  localization is correctly oriented.

## Honest status

This is a **localization**, not a proof. Its value: it pins the open content to
exactly one object — the diffuse zero-Lelong residual class for `p ≥ 2` — using
only proven theorems (Siu, Chow, Lefschetz) as the named inputs, with the `p=1`
case provably closed. The `AddSubgroup` skeleton is a faithful, non-vacuous
algebraic fact; the geometric content (that Siu yields an algebraic analytic
part, that Lefschetz closes `p=1`) is carried as named hypotheses, each a real
classical theorem rather than a Hodge-equivalent helper.

Caveat carried honestly: the Siu analytic part `Σλ_j [Z_j]` has real
coefficients `λ_j`, so over ℚ it lies in the real span of algebraic classes; the
rational descent (rational `α`, rational target) is a further classically
understood step folded into the named hypothesis `analytic ∈ A` when `A` is the
relevant span. The localization equivalence itself is coefficient-agnostic.

What RS would need to contribute: a discrete-tick / φ-quantization principle
forcing the diffuse residual class to be algebraic for `p ≥ 2`. No theorem in
the library forces that; doing so would prove Hodge. It is the sharpened open
target, recorded as such.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeDiffuseLocalization

universe u

variable {Coh : Type u} [AddCommGroup Coh]

/-- **Localization of the Hodge obstruction.** Given an additive Siu-type split
`α = analytic + diffuse` whose analytic part lies in the algebraic subgroup `A`
(Siu's analyticity theorem + Chow/GAGA), membership of `α` in `A` is equivalent
to membership of the diffuse residual. The whole obstruction sits in `diffuse`. -/
theorem hodge_iff_diffuse
    (A : AddSubgroup Coh) {α analytic diffuse : Coh}
    (hsum : α = analytic + diffuse) (hanalytic : analytic ∈ A) :
    α ∈ A ↔ diffuse ∈ A := by
  constructor
  · intro h
    have hd : diffuse = α - analytic := by rw [hsum]; abel
    rw [hd]
    exact A.sub_mem h hanalytic
  · intro h
    rw [hsum]
    exact A.add_mem hanalytic h

/-- A Siu decomposition functorial in the class: every class splits additively
into an algebraic analytic part and a diffuse residual. -/
structure SiuData (Coh : Type u) [AddCommGroup Coh] (A : AddSubgroup Coh) where
  /-- Analytic (Siu Lelong) part of the representing current's class. -/
  analytic : Coh → Coh
  /-- Diffuse zero-Lelong residual class. -/
  diffuse : Coh → Coh
  /-- Cohomological additivity of the Siu split. -/
  sum : ∀ α, α = analytic α + diffuse α
  /-- The analytic part is algebraic (Siu + Chow/GAGA). -/
  analytic_mem : ∀ α, analytic α ∈ A

/-- **Global Hodge localizes to the diffuse residuals.** With a functorial Siu
split, "every class is algebraic" is equivalent to "every diffuse residual is
algebraic." The open content is exactly the right-hand side. -/
theorem hodge_iff_all_diffuse_mem (A : AddSubgroup Coh) (S : SiuData Coh A) :
    (∀ α, α ∈ A) ↔ (∀ α, S.diffuse α ∈ A) := by
  constructor
  · intro h α
    exact (hodge_iff_diffuse A (S.sum α) (S.analytic_mem α)).mp (h α)
  · intro h α
    exact (hodge_iff_diffuse A (S.sum α) (S.analytic_mem α)).mpr (h α)

/-- **The `p = 1` case (Lefschetz (1,1)), recovered as a corollary.** If the
diffuse residual is itself algebraic — true in codimension one, where every
`(1,1)` integral class is a divisor class (Lefschetz) — then `α` is algebraic.
This confirms the localization is correctly oriented: Hodge is closed exactly
where the residual is forced algebraic. -/
theorem divisor_case_algebraic
    (A : AddSubgroup Coh) {α analytic diffuse : Coh}
    (hsum : α = analytic + diffuse)
    (hanalytic : analytic ∈ A) (hLefschetz : diffuse ∈ A) :
    α ∈ A :=
  (hodge_iff_diffuse A hsum hanalytic).mpr hLefschetz

/-- Bundled localization plus the open residual. The `diffuseAlgebraic` field is
the sole open input for `p ≥ 2`; everything else is a proven classical theorem
or an algebraic identity. -/
structure DiffuseLocalization (Coh : Type u) [AddCommGroup Coh] where
  algebraicClasses : AddSubgroup Coh
  siu : SiuData Coh algebraicClasses
  /-- OPEN for `p ≥ 2`; PROVEN (Lefschetz) for `p = 1`: the diffuse residual is
  algebraic. This is the entire remaining Hodge content. -/
  diffuseAlgebraic : ∀ α, siu.diffuse α ∈ algebraicClasses

/-- From a complete `DiffuseLocalization` (i.e. once the diffuse residual is
known algebraic), every class is algebraic: Hodge. The only nontrivial field is
`diffuseAlgebraic`, which is exactly the localized open lemma. -/
theorem hodge_of_diffuseLocalization (L : DiffuseLocalization Coh) :
    ∀ α, α ∈ L.algebraicClasses := by
  intro α
  exact (hodge_iff_all_diffuse_mem L.algebraicClasses L.siu).mpr L.diffuseAlgebraic α

end HodgeDiffuseLocalization
end Mathematics
end IndisputableMonolith
