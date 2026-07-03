import Mathlib
import IndisputableMonolith.Masses.GoldenMonodromyReturn

/-!
# Golden Torsion and the Alexander-Asymmetry Obstruction (GDB Stage 1)

`Masses/GoldenMonodromyReturn.lean` (GR) banked the return map
`returnMap k = !![0,1;1,k]` with `trace = k`, `det = −1`, and characteristic polynomial
`X² − k·X − 1` (theorem `returnMap_charpoly`), golden exactly at `k = 1`.
`Masses/GoldenMonodromyCarrier.lean` banked the explicit finite ℤ-chain carrier with `H₁ ≅ ℤ²`
and the monodromy inducing `returnMap (linkingNumber cr)` on `H₁`.

A 7-model director panel (debate + Fable-5 judge, 2026-07-02) greenlit the **GD Carrier Bridge
(repaired)**: the recognition carrier is the **nonorientable golden mapping torus** (the ℤ/2
orientation quotient of the `F`-cat-map bundle), **not** an `S³` link complement. Two banked facts
force the nonorientable reading, and this module discharges the algebraic half of Stage 1
(`carrier_torsion_golden`) as a THEOREM-grade finite certificate.

## The two banked obstructions to the `S³` reading

1. **`det F = −1`** (`returnMap_det`). A fibered link in `S³` has an orientation-*preserving*
   monodromy of its Seifert fiber, which acts on the fiber's `H₁` inside the symplectic group,
   hence with determinant `+1`. `det = −1` is orientation-*reversing*: incompatible with a
   fibered `S³` link, consistent with the nonorientable mapping torus.
2. **Alexander asymmetry.** The Alexander polynomial of a link in `S³` is reciprocal-symmetric,
   `Δ(t) ≐ Δ(t⁻¹)` up to units `±t^m`. The carrier's torsion polynomial is `Δ_k(t) = t² − k·t − 1`
   (the monodromy characteristic polynomial `det(tI − F)`), and this module proves
   `Δ_k` is reciprocal-symmetric (up to sign) **iff `k = 0`**. So the **golden** value `k = 1`
   gives `Δ_1 = t² − t − 1`, which is provably **not** Alexander-symmetric: the golden carrier
   cannot be an `S³` link complement.

## What this module proves (all THEOREM-grade, `#print axioms` = Mathlib base only)

For the torsion polynomial `torsionPoly k := (returnMap k).charpoly`:

* `torsionPoly_eq` — `torsionPoly k = X² − C k · X − 1` (the twisted determinant of the banked
  complex, up to the trivial `±t^k` unit, is the return-map char poly).
* `torsionPoly_golden` — `torsionPoly 1 = X² − X − 1`, the T6 golden minimal polynomial.
* `torsion_const_eq_det` / `extreme_antisymmetric` — the constant coefficient is `det = −1` and the
  leading coefficient is `+1`, so the extreme pair `(coeff 0, coeff 2) = (−1, +1)` is anti-palindromic
  **for every `k`**: the `det = −1` reciprocal signature, present independent of the linking number.
* `alexanderSymmetric_iff` — `Δ_k` is reciprocal-symmetric-up-to-sign **iff `k = 0`**.
* `torsion_golden_not_alexanderSymmetric` — the golden `Δ_1 = t² − t − 1` is **not** Alexander
  symmetric (the `S³` exclusion), routed through the banked charpoly.
* Differential oracle: `alexanderSymmetric 0` (unlink control, symmetric), and both the golden
  (`k = 1`) and clasp (`k = 2`) fail — the golden case is a genuine selection, not a relabeling.

## Honest status

- The algebra above is THEOREM-grade on already-banked integer data.
- **MODEL premise (stated, not asserted as THEOREM):** that an `S³`-link Alexander polynomial is
  reciprocal-symmetric and that the carrier's torsion polynomial is `det(tI − F)` are standard
  topological identifications, cited to justify the *reading* of these algebraic facts as the
  `S³`-exclusion / nonorientable-mapping-torus certificate. The Lean content is the obstruction
  itself: any `S³`-link identification of the golden carrier would require an Alexander symmetry
  the golden torsion polynomial provably lacks.
- **OPEN (later GDB stages):** the sign-character twisted `H₁` comparison (Stage 2), the order-2
  deck chain automorphism (Stage 3), and the full marked `ChainHomotopyEquiv` (Stage 4).
-/

namespace IndisputableMonolith
namespace Masses
namespace GoldenTorsionAlexander

open Polynomial
open IndisputableMonolith.Masses.GoldenMonodromyReturn

/-! ## The torsion polynomial and its reciprocal -/

/-- **The torsion polynomial of the carrier at linking number `k`.** Reidemeister/Alexander
torsion of the mapping torus of the monodromy `F` is `det(tI − F) = charpoly F` up to a `±t^k`
unit; we take this canonical polynomial representative. -/
noncomputable def torsionPoly (k : ℤ) : Polynomial ℤ := (returnMap k).charpoly

/-- **Closed form.** `torsionPoly k = X² − C k · X − 1` (the banked `returnMap_charpoly`). -/
theorem torsionPoly_eq (k : ℤ) : torsionPoly k = X ^ 2 - C k * X - 1 :=
  returnMap_charpoly k

/-- **Golden minimal polynomial at unit linking.** `torsionPoly 1 = X² − X − 1`. -/
theorem torsionPoly_golden : torsionPoly 1 = X ^ 2 - X - 1 :=
  returnMap_one_charpoly

/-- **The reciprocal (reversed) polynomial** `t² · Δ_k(t⁻¹) = −X² − C k · X + 1`. For a degree-2
polynomial with nonzero constant term, `Δ_k ≐ Δ_k(t⁻¹)` up to `±t^m` units collapses to
`Δ_k = ± recipPoly k` (the `t^m` factor is fixed to `m = 0` by degree matching). -/
noncomputable def recipPoly (k : ℤ) : Polynomial ℤ := -X ^ 2 - C k * X + 1

/-! ## Coefficient bookkeeping -/

theorem torsion_coeff0 (k : ℤ) : (torsionPoly k).coeff 0 = -1 := by
  rw [torsionPoly_eq]
  simp [coeff_sub, coeff_X_pow, coeff_one]

theorem torsion_coeff1 (k : ℤ) : (torsionPoly k).coeff 1 = -k := by
  rw [torsionPoly_eq]
  simp only [coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_one]
  norm_num

theorem torsion_coeff2 (k : ℤ) : (torsionPoly k).coeff 2 = 1 := by
  rw [torsionPoly_eq]
  simp [coeff_sub, coeff_X_pow, coeff_one]
  rw [← C_eq_intCast k, coeff_C]
  norm_num

theorem recip_coeff0 (k : ℤ) : (recipPoly k).coeff 0 = 1 := by
  unfold recipPoly
  simp [coeff_add, coeff_sub, coeff_neg, coeff_X_pow, coeff_one]

theorem recip_coeff1 (k : ℤ) : (recipPoly k).coeff 1 = -k := by
  unfold recipPoly
  simp only [coeff_add, coeff_sub, coeff_neg, coeff_X_pow, coeff_C_mul, coeff_X, coeff_one]
  norm_num

theorem recip_coeff2 (k : ℤ) : (recipPoly k).coeff 2 = -1 := by
  unfold recipPoly
  simp [coeff_add, coeff_sub, coeff_neg, coeff_X_pow, coeff_one]
  rw [← C_eq_intCast k, coeff_C]
  norm_num

/-! ## The `det = −1` reciprocal signature (present for every `k`) -/

/-- The constant coefficient of the torsion polynomial **is** the banked determinant `det F = −1`. -/
theorem torsion_const_eq_det (k : ℤ) : (torsionPoly k).coeff 0 = (returnMap k).det := by
  rw [torsion_coeff0, returnMap_det]

/-- **The extreme coefficients are anti-palindromic for every `k`.** `(coeff 0, coeff 2) = (−1, +1)`,
so `coeff 0 = − coeff 2`. This is the `det = −1` reciprocal signature: the leading/constant pair is
always anti-symmetric, independent of the linking number. -/
theorem extreme_antisymmetric (k : ℤ) :
    (torsionPoly k).coeff 0 = -(torsionPoly k).coeff 2 := by
  rw [torsion_coeff0, torsion_coeff2]

/-! ## Alexander (reciprocal) symmetry, and its failure at the golden value -/

/-- **Alexander (reciprocal) symmetry up to sign.** `Δ_k` is reciprocal-symmetric up to units iff
it equals `± recipPoly k`. For a degree-2 polynomial with nonzero constant term this is the exact
translation of `Δ_k(t) ≐ Δ_k(t⁻¹)`. -/
def alexanderSymmetric (k : ℤ) : Prop :=
  torsionPoly k = recipPoly k ∨ torsionPoly k = -recipPoly k

/-- The palindromic branch `Δ_k = recipPoly k` is **impossible** for every `k`: the leading
coefficients disagree (`+1` vs `−1`). -/
theorem not_torsion_eq_recip (k : ℤ) : torsionPoly k ≠ recipPoly k := by
  intro h
  have h2 : (torsionPoly k).coeff 2 = (recipPoly k).coeff 2 := by rw [h]
  rw [torsion_coeff2, recip_coeff2] at h2
  norm_num at h2

/-- **The Alexander-symmetry characterization.** `Δ_k` is reciprocal-symmetric-up-to-sign **iff
`k = 0`**. The palindromic branch never holds; the anti-palindromic branch `Δ_k = −recipPoly k`
holds iff the `X`-coefficient vanishes, i.e. iff `k = 0`. -/
theorem alexanderSymmetric_iff (k : ℤ) : alexanderSymmetric k ↔ k = 0 := by
  constructor
  · rintro (h | h)
    · exact absurd h (not_torsion_eq_recip k)
    · -- `Δ_k = − recipPoly k`; compare `coeff 1`: `−k = −(−k) = k`, so `k = 0`.
      have h1 : (torsionPoly k).coeff 1 = (-recipPoly k).coeff 1 := by rw [h]
      rw [torsion_coeff1, coeff_neg, recip_coeff1] at h1
      omega
  · intro hk
    subst hk
    right
    -- `torsionPoly 0 = X² − 1` and `− recipPoly 0 = X² − 1`.
    rw [torsionPoly_eq, recipPoly, map_zero]
    ring

/-- **The `S³` exclusion (golden case).** The golden torsion polynomial `Δ_1 = t² − t − 1` is
**not** Alexander-symmetric. Hence the golden carrier is not a fibered `S³` link complement; the
panel's nonorientable golden mapping torus is the surviving reading. -/
theorem torsion_golden_not_alexanderSymmetric : ¬ alexanderSymmetric 1 := by
  rw [alexanderSymmetric_iff]; norm_num

/-! ## The differential oracle: only the golden value is selected out by asymmetry... and controls -/

/-- **Unlink control (`k = 0`) is Alexander-symmetric.** `Δ_0 = t² − 1` satisfies
`Δ_0 = − recipPoly 0`. The two-component unlink is a genuine `S³` link, so its torsion *should*
be reciprocal-symmetric — the honest differential: symmetry breaks at `k = 1`, not everywhere. -/
theorem torsion_unlink_alexanderSymmetric : alexanderSymmetric 0 := by
  rw [alexanderSymmetric_iff]

/-- **Clasp control (`k = 2`) is not Alexander-symmetric.** -/
theorem torsion_clasp_not_alexanderSymmetric : ¬ alexanderSymmetric 2 := by
  rw [alexanderSymmetric_iff]; norm_num

/-! ## Certificate bundling GDB Stage 1 -/

/-- THEOREM-grade certificate for **GDB Stage 1** (`carrier_torsion_golden` + Alexander-asymmetry
obstruction): the carrier torsion polynomial is the banked return-map characteristic polynomial
`X² − k·X − 1`, equals the T6 golden minimal polynomial `X² − X − 1` at unit linking, carries the
`det = −1` reciprocal signature for every `k`, is Alexander-symmetric iff `k = 0`, and in particular
the **golden** case `k = 1` is provably **not** Alexander-symmetric — the algebraic obstruction
excluding the `S³`-link reading in favor of the nonorientable golden mapping torus.

**MODEL premise (not asserted here):** the topological identifications (torsion `= det(tI − F)`;
`S³`-link Alexander polynomials are reciprocal-symmetric) that license reading these algebraic facts
as the `S³` exclusion. -/
structure GoldenTorsionAlexanderCert : Prop where
  torsion_eq : ∀ k : ℤ, torsionPoly k = X ^ 2 - C k * X - 1
  torsion_golden : torsionPoly 1 = X ^ 2 - X - 1
  const_is_det : ∀ k : ℤ, (torsionPoly k).coeff 0 = (returnMap k).det
  extreme_antisym : ∀ k : ℤ, (torsionPoly k).coeff 0 = -(torsionPoly k).coeff 2
  symmetric_iff_unlinked : ∀ k : ℤ, alexanderSymmetric k ↔ k = 0
  golden_excludes_s3 : ¬ alexanderSymmetric 1
  differential : alexanderSymmetric 0
      ∧ (¬ alexanderSymmetric 1) ∧ (¬ alexanderSymmetric 2)

theorem goldenTorsionAlexanderCert_holds : GoldenTorsionAlexanderCert where
  torsion_eq := torsionPoly_eq
  torsion_golden := torsionPoly_golden
  const_is_det := torsion_const_eq_det
  extreme_antisym := extreme_antisymmetric
  symmetric_iff_unlinked := alexanderSymmetric_iff
  golden_excludes_s3 := torsion_golden_not_alexanderSymmetric
  differential := ⟨torsion_unlink_alexanderSymmetric,
    torsion_golden_not_alexanderSymmetric, torsion_clasp_not_alexanderSymmetric⟩

end GoldenTorsionAlexander
end Masses
end IndisputableMonolith
