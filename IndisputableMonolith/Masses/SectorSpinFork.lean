import Mathlib
import IndisputableMonolith.Masses.SectorChannelMultiplicity
import IndisputableMonolith.Masses.SectorDimensionDerivation
import IndisputableMonolith.Masses.ChamberSolidAngleBridge

/-!
# The sector spin-fork: the proven Z₂ embedding ambiguity and the signed channel spectrum

`SectorDimensionDerivation` proved that a `ValidSectorEmbedding` (a bijection of `Fin 3` that is
equivariant for the conjugation/duality involutions) FORCES the lepton to the loop dimension
(`e 1 = 1`) and the two colored sectors to the dual orbit `{0,2}`, but leaves a residual **2-fold
ambiguity**: the colored assignment can be `(e 0, e 2) = (0,2)` OR `(2,0)`, and BOTH are valid. The
channel multiplicity is invariant under this Z₂ (lepton 1, colored 3 either way), so the Z₂ is
multiplicity-invisible.

This module forks on that proven Z₂ and asks whether it is **physical** (a chirality/spin label) or
**gauge** (an unobservable relabeling). The honest test the panel demanded: attach a SIGN to the two
branches, build the resulting signed channel spectrum, and state a falsifier against an observed
signed adjacent-generation coupling step. If the observed signed coupling lands on exactly one
branch, the Z₂ is physical; if it is observationally identical across branches, the Z₂ is gauge and
this is a pure-math note.

## Honest status (read before citing)

* THEOREM (axiom-clean): the two-case enumeration `validSectorEmbedding_cases`, the signed integer
  spectrum `signedMult ∈ {−3,−1,1,3}`, its achievability (all four signs realized by `id` and
  `dimDual`), and the falsifier `signedChannelCorrection_falsifier`.
* HYPOTHESIS, named falsifier: the IDENTIFICATION of this Z₂ with physical chirality/spin. The sign
  is INJECTED by `spinOfEmbedding` (a definition), not derived from the kernel. The falsifier is the
  numeric sign-match `signedChannelCorrection_falsifier` against a measured coupling, NOT "do the
  branches differ" (they differ only by the injected sign).
* KNOWN STRUCTURAL RISK (flagged, not buried): the model's Z₂ is a GLOBAL label of the embedding;
  `e 1 = 1` for both branches, so the Z₂ acts trivially on the lepton's DIMENSION while physical
  chirality does not act trivially on a lepton. If that mismatch is structural it kills the
  identification. Cheap to find out; either outcome is publishable.
-/

namespace IndisputableMonolith
namespace Masses
namespace SectorSpinFork

open SectorChannelMultiplicity SectorDimensionDerivation

/-! ## The proven Z₂: two-case enumeration of valid embeddings -/

/-- **THEOREM (the Z₂, enumerated).** Every `ValidSectorEmbedding` fixes the lepton at the loop
    dimension and sends the colored pair to the dual orbit in exactly one of two ways. This is the
    provable backbone: bijectivity + forced-lepton + dual-orbit collapse to a clean 2-case split. -/
theorem validSectorEmbedding_cases (e : Fin 3 → Fin 3) :
    ValidSectorEmbedding e →
      e 1 = 1 ∧ ((e 0 = 0 ∧ e 2 = 2) ∨ (e 0 = 2 ∧ e 2 = 0)) := by
  decide +revert

/-! ## The injected sign and the signed multiplicity -/

/-- The injected spin/chirality sign of an embedding: `+1` if the up-type colored sector maps to
    dimension `0`, `−1` if to dimension `2`. **This sign is a DEFINITION, not a derivation** — it is
    the candidate chirality label whose physicality the falsifier below tests. -/
def spinOfEmbedding (e : Fin 3 → Fin 3) : ℤ := if e 0 = 0 then 1 else -1

/-- The signed channel multiplicity: the (proven, embedding-invariant) geometric multiplicity of the
    sector's dimension, carrying the injected branch sign. Values lie in `{−3,−1,1,3}`. -/
def signedMult (e : Fin 3 → Fin 3) (s : Fin 3) : ℤ :=
  spinOfEmbedding e * (geomChannelMultiplicity (e s).val : ℤ)

/-- **THEOREM (the signed integer spectrum).** For any map `Fin 3 → Fin 3`, the signed multiplicity
    is one of the four values `{−3,−1,1,3}`: the multiplicity magnitude is `1` (lepton) or `3`
    (colored), and the sign is `±1`. Holds even without validity (the magnitude set is already
    `{1,3}`); validity is what pins WHICH sector gets which magnitude. -/
theorem signedMult_mem (e : Fin 3 → Fin 3) (s : Fin 3) :
    signedMult e s ∈ ({-3, -1, 1, 3} : Finset ℤ) := by
  decide +revert

/-- **THEOREM (achievability: all four signed values are realized).** The identity embedding
    (spin `+1`) realizes `+3` (colored) and `+1` (lepton); the `dimDual` embedding (spin `−1`)
    realizes `−3` and `−1`. So the spectrum is genuinely four-valued, not collapsed. -/
theorem signedMult_surj :
    signedMult id 0 = 3 ∧ signedMult id 1 = 1 ∧
    signedMult dimDual 0 = -3 ∧ signedMult dimDual 1 = -1 := by
  decide

/-! ## The signed channel correction and the falsifier -/

/-- The signed channel correction: the boundary quantum `1/(4π)` times the signed multiplicity.
    Honest value spectrum `{±1/(4π), ±3/(4π)}` (defeq to `signedMult /(4π)`). -/
noncomputable def signedChannelCorrection (e : Fin 3 → Fin 3) (s : Fin 3) : ℝ :=
  (signedMult e s : ℝ) / (4 * Real.pi)

/-- **THEOREM (the signed spectrum, explicitly).** Every signed channel correction equals
    `k/(4π)` for some `k ∈ {−3,−1,1,3}`. This is the exact set the model predicts an observed
    signed coupling step must fall in. -/
theorem signedChannelCorrection_spectrum (e : Fin 3 → Fin 3) (s : Fin 3) :
    ∃ k ∈ ({-3, -1, 1, 3} : Finset ℤ),
      signedChannelCorrection e s = (k : ℝ) / (4 * Real.pi) :=
  ⟨signedMult e s, signedMult_mem e s, rfl⟩

/-- **THEOREM (the falsifier).** If a measured signed adjacent-generation coupling step `c` does
    NOT equal `k/(4π)` for any `k ∈ {−3,−1,1,3}`, then NO sector under ANY embedding reproduces it:
    the model is refuted. This is the honest physics test — a numeric sign-and-magnitude match
    against a real observable, parameterized by the measurement `c` (no fabricated number). The Z₂
    is physical iff the measured `c` matches exactly one branch's sign; gauge iff the branches are
    observationally identical. -/
theorem signedChannelCorrection_falsifier
    (c : ℝ)
    (h : ∀ k ∈ ({-3, -1, 1, 3} : Finset ℤ), c ≠ (k : ℝ) / (4 * Real.pi)) :
    ∀ (e : Fin 3 → Fin 3) (s : Fin 3), signedChannelCorrection e s ≠ c := by
  intro e s heq
  obtain ⟨k, hk, hval⟩ := signedChannelCorrection_spectrum e s
  exact h k hk (by rw [← hval, heq])

/-! ## The honest residual, stated as a theorem (the structural risk, not buried) -/

/-- **THEOREM (the lepton-triviality mismatch, exposed).** Under EVERY valid embedding the lepton's
    DIMENSION is fixed (`e 1 = 1`), so its multiplicity magnitude `geomChannelMultiplicity (e 1).val`
    is `1` independent of the branch. The Z₂'s only effect on the lepton is the GLOBAL sign carried
    by `spinOfEmbedding`, not a per-lepton chirality. This is the structural risk to the
    chirality identification, stated as a fact rather than hidden. -/
theorem lepton_dimension_branch_invariant (e : Fin 3 → Fin 3) :
        ValidSectorEmbedding e → geomChannelMultiplicity (e 1).val = 1 := by
  decide +revert

/-! ## The spin-fork cert -/

/-- **Sector Spin-Fork Cert.**

    THEOREM content (axiom-clean):
    * `cases`: the proven Z₂ enumerated into two colored-assignment branches.
    * `spectrum`: every signed channel correction is `k/(4π)`, `k ∈ {−3,−1,1,3}`.
    * `surj`: all four signed values realized (`id` gives `+`, `dimDual` gives `−`).
    * `falsifier`: an observed signed coupling outside `{±1/(4π),±3/(4π)}` refutes the model.
    * `lepton_inv`: the lepton dimension is branch-invariant (the structural-risk fact).

    HYPOTHESIS (named falsifier = `falsifier`): the identification of this Z₂ with physical
    chirality. The sign is injected by `spinOfEmbedding`; physicality is decided by the numeric
    sign-match, not by the existence of two branches. -/
structure SpinForkCert where
  cases :
    ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e →
      e 1 = 1 ∧ ((e 0 = 0 ∧ e 2 = 2) ∨ (e 0 = 2 ∧ e 2 = 0))
  spectrum :
    ∀ (e : Fin 3 → Fin 3) (s : Fin 3),
      ∃ k ∈ ({-3, -1, 1, 3} : Finset ℤ),
        signedChannelCorrection e s = (k : ℝ) / (4 * Real.pi)
  surj :
    signedMult id 0 = 3 ∧ signedMult id 1 = 1 ∧
    signedMult dimDual 0 = -3 ∧ signedMult dimDual 1 = -1
  falsifier :
    ∀ (c : ℝ), (∀ k ∈ ({-3, -1, 1, 3} : Finset ℤ), c ≠ (k : ℝ) / (4 * Real.pi)) →
      ∀ (e : Fin 3 → Fin 3) (s : Fin 3), signedChannelCorrection e s ≠ c
  lepton_inv :
    ∀ e : Fin 3 → Fin 3, ValidSectorEmbedding e → geomChannelMultiplicity (e 1).val = 1

/-- **The spin-fork cert instance.** Bundles the proven Z₂ enumeration, the signed spectrum, its
    achievability, the numeric falsifier, and the lepton-triviality structural-risk fact. -/
def spinForkCert : SpinForkCert where
  cases := fun e he => validSectorEmbedding_cases e he
  spectrum := signedChannelCorrection_spectrum
  surj := signedMult_surj
  falsifier := signedChannelCorrection_falsifier
  lepton_inv := lepton_dimension_branch_invariant

end SectorSpinFork
end Masses
end IndisputableMonolith
