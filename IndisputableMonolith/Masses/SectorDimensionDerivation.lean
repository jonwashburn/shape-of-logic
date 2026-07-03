import Mathlib
import IndisputableMonolith.Masses.SectorChannelMultiplicity

/-!
# Sector → Dimension assignment: forced by duality-equivariance (the residual seam)

`SectorChannelMultiplicity` left ONE thing tagged MODEL: the per-sector channel
multiplicity rule

  `geomChannelMultiplicity d = if d = loopDimension then 1 else vertexDegree`

reads off the multiplicity from the COUPLING DIMENSION `d`, but *which physics sector
sits at which dimension* (lepton at the self-dual `d = 1`, the colored quarks at the
dual orbit `{0, 2}`) was a hand-set identification, not a theorem.

This module forces that identification from duality-equivariance, and is honest about
exactly how far the forcing reaches.

## The two involutions

* On coupling dimensions, the duality `dimDual d = 2 − d` (Fin 3 arithmetic): fixed point
  `1`, non-trivial orbit `{0, 2}`. This is the same `d ↦ 2 − d` already load-bearing in
  `SectorDependentTorsion` and recorded in `SectorChannelMultiplicity.loopDimension_self_dual`.
* On physics sectors (`0 = up`, `1 = lepton`, `2 = down`), the conjugation `secConj s = 2 − s`:
  the lepton is self-conjugate (colorless), the up and down quarks are a conjugate pair.
  This conjugation structure is the ONE physics input that remains (see honest scope below).

## What is forced (THEOREM) and what is not

A `ValidSectorEmbedding` is a bijection `e : Fin 3 → Fin 3` that is equivariant for these two
involutions: `e (secConj s) = dimDual (e s)`. Then, proved by `decide` over the finite function
space (no answer baked in):

* `valid_forces_lepton_to_loop`: every valid embedding sends the lepton (`1`, the conjugation
  fixed point) to the loop dimension (`1`, the duality fixed point). The colorless sector lands
  at the self-dual dimension necessarily, by equivariance, not by choice.
* `valid_forces_colored_to_orbit`: every valid embedding sends the colored pair `{up, down}` into
  the dual orbit `{0, 2}`.
* `assignment_not_unique`: the sector→dimension map is NOT unique — both the identity and `dimDual`
  are valid embeddings, and they disagree on where `up` goes (`0` vs `2`). So a residual 2-fold
  freedom survives within the colored orbit.
* `valid_forces_multiplicity` (THE payoff): despite that residual freedom, every valid embedding
  yields the SAME channel multiplicities — lepton `1`, both colored sectors `3` — because both
  orbit dimensions give the vertex degree. The orbit ambiguity is MULTIPLICITY-INVISIBLE.

## Honest status (the seam is reduced, not eliminated)

THEOREM: given the conjugation structure on sectors, the sector → **multiplicity** map (the only
part that touches the physics, the `1` vs `3` split) is forced by duality-equivariance. The MODEL
identification in `geomChannelMultiplicity` is now backed by `valid_forces_multiplicity`.

REMAINING INPUT (not eliminated): the conjugation structure itself — "the lepton is self-conjugate
(colorless) and the two quarks are a conjugate pair" — is supplied, not derived here. The boundary
condition is relocated from "which dimension does each sector take?" (now answered up to a
multiplicity-invariant swap) to "which sector is self-conjugate?", which is a more basic and
standard datum. This is genuine progress: the seam that affected the kernel value is closed; the
residual input is weaker and more defensible. Per honest tagging, independence-up-to-input is not
unconditional derivation, so the conjugation structure is named, not hidden.
-/

namespace IndisputableMonolith
namespace Masses
namespace SectorDimensionDerivation

open SectorChannelMultiplicity

/-- The coupling-dimension duality `d ↦ 2 − d` on `Fin 3`: fixed point `1`, orbit `{0, 2}`.
    This is the `Fin 3` form of the `d ↦ 2 − d` already load-bearing in `SectorDependentTorsion`. -/
def dimDual (d : Fin 3) : Fin 3 := 2 - d

/-- The sector conjugation `s ↦ 2 − s` on `Fin 3` (`0 = up`, `1 = lepton`, `2 = down`):
    the lepton (`1`) is self-conjugate, the up/down quarks (`0`/`2`) are a conjugate pair. -/
def secConj (s : Fin 3) : Fin 3 := 2 - s

/-- **THEOREM.** `1` is the unique fixed point of the coupling-dimension duality on `Fin 3`. -/
theorem dimDual_fixed_iff (d : Fin 3) : dimDual d = d ↔ d = 1 := by revert d; decide

/-- **THEOREM.** `1` (the lepton) is the unique fixed point of the sector conjugation on `Fin 3`. -/
theorem secConj_fixed_iff (s : Fin 3) : secConj s = s ↔ s = 1 := by revert s; decide

/-- A valid sector→dimension embedding: a bijection `e : Fin 3 → Fin 3` that is equivariant for
    the sector conjugation and the coupling-dimension duality, `e (secConj s) = dimDual (e s)`.
    The predicate is built ONLY from the two involutions and bijectivity — the answer
    (`lepton ↦ 1`) is NOT baked in. Reducible so `decide` can see the finite decidability. -/
@[reducible] def ValidSectorEmbedding (e : Fin 3 → Fin 3) : Prop :=
  Function.Bijective e ∧ ∀ s, e (secConj s) = dimDual (e s)

/-- **THEOREM (equivariance forces the lepton to the loop dimension).** Every valid embedding
    sends the lepton (`1`, the conjugation fixed point) to the loop dimension (`1`, the duality
    fixed point): a bijection equivariant for two involutions must carry the unique fixed point
    to the unique fixed point. The colorless sector lands at the self-dual dimension necessarily.
    `by decide` over the finite function space `Fin 3 → Fin 3`. -/
theorem valid_forces_lepton_to_loop :
    ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e → e 1 = 1 := by decide

/-- **THEOREM (equivariance forces the colored pair into the dual orbit).** Every valid embedding
    sends `up` (`0`) and `down` (`2`) into the non-trivial dual orbit `{0, 2}`. `by decide`. -/
theorem valid_forces_colored_to_orbit :
    ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e →
      (e 0 = 0 ∨ e 0 = 2) ∧ (e 2 = 0 ∨ e 2 = 2) := by decide

/-- **THEOREM (the identity is a valid embedding).** Witness with `up ↦ 0`. -/
theorem valid_id : ValidSectorEmbedding (id : Fin 3 → Fin 3) := by decide

/-- **THEOREM (the duality itself is a valid embedding).** Witness with `up ↦ 2`. -/
theorem valid_dimDual : ValidSectorEmbedding dimDual := by decide

/-- **THEOREM (the sector→dimension map is NOT unique).** There are two valid embeddings — the
    identity and the duality — that disagree on where `up` goes (`0` vs `2`). A residual 2-fold
    freedom survives within the colored orbit. This is the honest counterpart to
    `valid_forces_multiplicity`: the dimension assignment is forced only up to a swap of the two
    colored dimensions. -/
theorem assignment_not_unique :
    ∃ e₁ e₂ : Fin 3 → Fin 3,
      ValidSectorEmbedding e₁ ∧ ValidSectorEmbedding e₂ ∧ e₁ 0 ≠ e₂ 0 :=
  ⟨id, dimDual, valid_id, valid_dimDual, by decide⟩

/-- **THEOREM (the payoff: multiplicity is forced despite the orbit ambiguity).** For every valid
    embedding `e`, the channel multiplicity read off the assigned dimension is the SAME — lepton
    `1`, both colored sectors `3` — because the residual orbit swap is multiplicity-invisible
    (both orbit dimensions give the vertex degree `3`). This is the theorem that backs the MODEL
    identification in `SectorChannelMultiplicity.geomChannelMultiplicity`: the sector → multiplicity
    map (the `1` vs `3` split that touches the kernel) is forced by duality-equivariance, not chosen.
    `by decide`. -/
theorem valid_forces_multiplicity :
    ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e →
      geomChannelMultiplicity (e 1).val = 1 ∧
      geomChannelMultiplicity (e 0).val = 3 ∧
      geomChannelMultiplicity (e 2).val = 3 := by decide

/-! ## Sector→dimension derivation cert -/

/-- **Sector→Dimension Derivation Cert: the residual seam, reduced by duality-equivariance.**

    THEOREM content (given the conjugation structure on sectors):
    * `lepton_forced`: equivariance sends the colorless lepton to the self-dual loop dimension.
    * `colored_forced`: equivariance sends the colored pair into the dual orbit `{0, 2}`.
    * `multiplicity_forced`: every valid embedding yields lepton `1`, colored `3` — the
      kernel-relevant `1` vs `3` split is forced, backing the MODEL rule in
      `geomChannelMultiplicity`.

    HONEST residual:
    * `not_unique`: the dimension assignment retains a 2-fold orbit ambiguity (identity vs duality),
      which is multiplicity-invisible. The conjugation structure ("lepton self-conjugate, quarks a
      conjugate pair") is the remaining named input; the boundary condition is relocated to that
      more basic datum, not eliminated. -/
structure SectorDimensionCert where
  /-- Equivariance forces the lepton to the loop dimension. -/
  lepton_forced : ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e → e 1 = 1
  /-- Equivariance forces the colored pair into the dual orbit `{0, 2}`. -/
  colored_forced : ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e →
    (e 0 = 0 ∨ e 0 = 2) ∧ (e 2 = 0 ∨ e 2 = 2)
  /-- The kernel-relevant multiplicity split (lepton `1`, colored `3`) is forced. -/
  multiplicity_forced : ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e →
    geomChannelMultiplicity (e 1).val = 1 ∧
    geomChannelMultiplicity (e 0).val = 3 ∧
    geomChannelMultiplicity (e 2).val = 3
  /-- The honest residual: the dimension assignment is not unique (a multiplicity-invisible
      2-fold orbit swap survives). -/
  not_unique : ∃ e₁ e₂ : Fin 3 → Fin 3,
    ValidSectorEmbedding e₁ ∧ ValidSectorEmbedding e₂ ∧ e₁ 0 ≠ e₂ 0

/-- **The sector→dimension derivation cert instance.** The kernel-relevant sector → multiplicity
    map is forced by duality-equivariance (THEOREM), with the dimension assignment forced up to a
    multiplicity-invisible orbit swap and the conjugation structure as the one remaining input. -/
def sectorDimensionCert : SectorDimensionCert where
  lepton_forced := valid_forces_lepton_to_loop
  colored_forced := valid_forces_colored_to_orbit
  multiplicity_forced := valid_forces_multiplicity
  not_unique := assignment_not_unique

end SectorDimensionDerivation
end Masses
end IndisputableMonolith
