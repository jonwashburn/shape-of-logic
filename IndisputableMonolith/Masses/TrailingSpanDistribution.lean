import Mathlib
import IndisputableMonolith.Masses.TrailingFoldBridge
import IndisputableMonolith.Masses.SectorDependentTorsion

/-!
# Trailing Span Distribution and Sign (Target T2)

This module carries the honest two-layer landing for the **span/sign** half of the
charged-lepton trailing torsion constant

  `δ_32 = −(φ/2) / Δr_32 = −(φ/2)/6`.

T1 (`TrailingFoldBridge`) forced the sector-independent **numerator** `φ/2`. T2 divides
that debit over the trailing rung span `Δr_32 = F = 6` (already a `native_decide` cube-count
theorem, `SectorDependentTorsion.lepton_step_23_eq`) and attaches the closure sign.

## The panel-vetted split (anti-circularity)

The bare statement `δ_32 = −(φ/2)/6` is a definition, not a derivation. The honest content
is a forcing chain from the two proved endpoints (numerator `φ/2`, span `6`) plus two explicit
physical premises, to the signed per-rung value.

- **THEOREM layer (proved here, no `sorry`, axiom-clean arithmetic):**
  * `trailingSpan_eq_six` — the denominator, re-exported from the cube-count theorem.
  * `reconstruct_total` — for any per-rung profile `f : Fin n → ℝ` (`n > 0`), the average
    share times the span reconstructs the total, `avgShare f · n = ∑ f`.
  * `universality_invariant` — `|δ_32| · Δr_32 = φ/2`. **Panel correction (2026-07-01):** this
    invariant tests the **T1 numerator universality** (the total debit is a sector-independent
    `φ/2`, recovered regardless of the span), NOT the S1 equidistribution premise. It holds for
    *any* sum-preserving profile because `|average| · N = |total|`.
  * `endpointProfile_sum` + `endpointProfile_not_uniform` — the concrete refutation of
    "invariant ⇒ uniform": an endpoint-concentrated profile on the 6 rungs sums to `φ/2`
    (so satisfies the invariant) yet is manifestly non-uniform. Proves S1 is not forced by the
    invariant; it is a genuine, separately-falsifiable modeling commitment.
  * `perRungTorsion_forced` / `delta32_forced` — the CONDITIONAL forcing theorems: given the
    T1 numerator, the span, S1 (equidistribution) and S2 (closure sign), every rung carries the
    same torsion `−(φ/2)/6`.

- **MODEL layer (explicit `Prop` premises, NOT proved; the irreducible physical input):**
  * `SpanEquidistributionPremise f` (S1): the sector-independent debit distributes *uniformly*
    over the `Δr_32` rung-increments (`∀ i j, f i = f j`). This is what collapses the profile to
    the single value `numerator / span`; without it the per-rung torsion varies. The
    endpoint counterexample above violates S1 while preserving the total, so S1 is non-vacuous.
  * `ClosureSignPremise sign` (S2): the generation cycle closes, so the debit is *paid back*
    (negative sign, `sign = −1`), not accrued.

## Live research bets (recorded, NOT closed; kill-conditions attached)

Two routes could upgrade a MODEL premise to THEOREM; both were checked cheaply against the
existing Lean and neither lands as written:

- **S1 upgrade (cube-symmetry transitivity).** IF the 6 rung-increments were a single orbit of
  a face-transitive cube symmetry, uniform shares would be forced. Blockers found: (a) the
  library proves the span *count* `= 6 = cube_faces' 3`, not a bijection increments↔faces;
  (b) `SectorDependentTorsion` carries the antipodal `conj` map, so the recognition-relevant
  symmetry plausibly respects opposite-face pairing → 3 antipodal pairs, not one orbit.
  KILL if the recognition group acts with 3 antipodal orbits on the faces.

- **S2 upgrade (discrete-Stokes / ledger conservation).** IF the debit's sub-chain closed to
  *identity* (`s₀ = sₙ`), `∮ δ = 0` would fix the sign topologically. Blocker: the T1 premise
  `OctaveClosurePremise` maps states across a golden **conjugate** ratio (`ρ ∈ {φ², φ⁻²}`), i.e.
  closure-up-to-conjugation, not identity. KILL unless the fold sub-chain returns to `s₀` with
  no conjugation twist.

## Honest status

CONDITIONAL forcing THEOREM (T1-numerator ∧ span=6 ∧ S1 ∧ S2 ⇒ `−(φ/2)/6`) + MODEL premises
S1, S2. Same tier as the T1 bridge. Composed with T1, the full δ_32 is CONDITIONAL on
{B1, B2, S1, S2}.

Lean status: no `sorry`; no new axioms beyond Mathlib base.
-/

namespace IndisputableMonolith
namespace Masses
namespace TrailingSpanDistribution

open Constants
open scoped BigOperators

noncomputable section

/-! ## THEOREM layer: the span (denominator) -/

/-- The trailing rung span `Δr_32`, re-exported from the cube-geometry count. -/
def trailingSpan : ℕ := SectorDependentTorsion.lepton_step_23

/-- `Δr_32 = F = 6`. Proved upstream by `native_decide` on the cube face count. -/
theorem trailingSpan_eq_six : trailingSpan = 6 :=
  SectorDependentTorsion.lepton_step_23_eq

/-! ## THEOREM layer: distribution arithmetic -/

/-- The per-rung *average* share of a distribution profile over the span. -/
def avgShare {n : ℕ} (f : Fin n → ℝ) : ℝ := (∑ j, f j) / (n : ℝ)

/-- **Reconstruction.** For any profile over `n > 0` rungs, the average share times the span
recovers the total debit. This is profile-shape-independent, which is why the invariant below
tests the total (T1), not the distribution (S1). -/
theorem reconstruct_total {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    avgShare f * (n : ℝ) = ∑ j, f j := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold avgShare
  field_simp

/-- Under uniform equidistribution, every rung carries the average share. This is the lemma S1
buys: it collapses an arbitrary profile to the single value `total / n`. -/
theorem uniform_perRung_constant {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ)
    (huni : ∀ i j, f i = f j) (i : Fin n) :
    f i = (∑ j, f j) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsum : (∑ j, f j) = (n : ℝ) * f i := by
    have hcongr : (∑ j, f j) = ∑ _j : Fin n, f i :=
      Finset.sum_congr rfl (fun j _ => huni j i)
    rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum, mul_comm (n : ℝ) (f i), mul_div_assoc, div_self hn', mul_one]

/-! ## THEOREM layer: the signed assembly and its value -/

/-- The signed per-rung torsion built from a sign, the numerator, and the span. -/
def signedPerRung (sign num : ℝ) (span : ℕ) : ℝ := sign * (num / (span : ℝ))

/-- The trailing lepton torsion constant, assembled from T1 (`num = φ/2`), the span (`6`),
and the closure sign (`−1`). -/
def delta32 : ℝ := signedPerRung (-1) (phi / 2) 6

/-- `δ_32 = −(φ/2)/6`. -/
theorem delta32_eq : delta32 = -(phi / 2) / 6 := by
  unfold delta32 signedPerRung
  push_cast
  ring

/-- The uniform per-rung share at the physical values: `(φ/2)/6 = φ/12`. -/
theorem perRungUniform_value : (phi / 2) / (6 : ℝ) = phi / 12 := by
  ring

/-! ## THEOREM layer: the sector-universality invariant (tests T1, not S1) -/

/-- **Sector-universality invariant.** `|δ_32| · Δr_32 = φ/2`. This recovers the T1 numerator
from the signed per-rung value: the *total* trailing debit is a sector-independent `φ/2`,
regardless of the span it divides over. It is the falsifiable content of the **numerator**
(T1), not of the equidistribution premise (S1) — see the endpoint counterexample below. -/
theorem universality_invariant : |delta32| * (trailingSpan : ℝ) = phi / 2 := by
  have hpos : (0 : ℝ) < phi / 2 := by have := Constants.phi_pos; linarith
  have h6 : ((6 : ℕ) : ℝ) = 6 := by norm_num
  rw [trailingSpan_eq_six, delta32_eq, h6]
  rw [abs_div, abs_neg, abs_of_pos hpos, abs_of_pos (show (0 : ℝ) < 6 by norm_num)]
  ring

/-! ## THEOREM layer: the invariant does NOT force uniformity (S1 is a real premise) -/

/-- An endpoint-concentrated distribution: the entire `φ/2` debit sits on the first rung. -/
def endpointProfile : Fin 6 → ℝ := fun i => if i = 0 then phi / 2 else 0

theorem endpointProfile_zero : endpointProfile 0 = phi / 2 := by
  unfold endpointProfile; rw [if_pos rfl]

theorem endpointProfile_one : endpointProfile 1 = 0 := by
  unfold endpointProfile; rw [if_neg (by decide : (1 : Fin 6) ≠ 0)]

/-- The endpoint profile still sums to the T1 numerator `φ/2`, so it satisfies the
universality invariant. -/
theorem endpointProfile_sum : (∑ i, endpointProfile i) = phi / 2 := by
  simp [endpointProfile]

/-- The endpoint profile is manifestly non-uniform. Combined with `endpointProfile_sum`, this
proves the invariant is blind to the distribution shape: it cannot force S1. -/
theorem endpointProfile_not_uniform :
    ¬ (∀ i j : Fin 6, endpointProfile i = endpointProfile j) := by
  intro h
  have hkey := h 0 1
  rw [endpointProfile_zero, endpointProfile_one] at hkey
  have := Constants.phi_pos
  linarith

/-! ## MODEL layer: the two explicit physical premises (NOT proved) -/

/-- **MODEL premise S1 (span equidistribution).** The sector-independent debit distributes
*uniformly* over the trailing rung-increments: every rung carries the same share. This is the
irreducible modeling commitment that lets the single value `numerator / span` stand in for each
rung's torsion. It is non-vacuous: `endpointProfile` preserves the total while violating it. -/
def SpanEquidistributionPremise {n : ℕ} (f : Fin n → ℝ) : Prop := ∀ i j, f i = f j

/-- **MODEL premise S2 (closure sign).** The generation cycle closes, so the trailing debit is
paid back on closure — a negative torsion (`sign = −1`), not an accrual. -/
def ClosureSignPremise (sign : ℝ) : Prop := sign = -1

/-- The per-rung torsion carried by rung `i` under a distribution profile `f` and a sign. -/
def perRungTorsion {n : ℕ} (sign : ℝ) (f : Fin n → ℝ) (i : Fin n) : ℝ := sign * f i

/-! ## THEOREM layer: the conditional forcing chain -/

/-- **CONDITIONAL forcing theorem (T2, per-rung form).** Given S1 (equidistribution), the T1
total `φ/2`, the span `6`, and S2 (closure sign), *every* rung carries the same torsion
`−(φ/2)/6`. S1 is load-bearing here: it is exactly what `uniform_perRung_constant` consumes to
collapse the profile to the single value. -/
theorem perRungTorsion_forced {n : ℕ} (hn : 0 < n)
    {sign : ℝ} (f : Fin n → ℝ)
    (hS1 : SpanEquidistributionPremise f)
    (htot : (∑ j, f j) = phi / 2)
    (hspan : n = 6)
    (hS2 : ClosureSignPremise sign)
    (i : Fin n) :
    perRungTorsion sign f i = -(phi / 2) / 6 := by
  have hs : sign = -1 := hS2
  have hfi : f i = (∑ j, f j) / (n : ℝ) := uniform_perRung_constant hn f hS1 i
  unfold perRungTorsion
  rw [hs, hfi, htot, hspan]
  push_cast
  ring

/-- **CONDITIONAL forcing theorem (T2, scalar form).** Given the T1 numerator, the span, and S2,
the signed per-rung assembly is `−(φ/2)/6`. -/
theorem delta32_forced
    {sign num : ℝ} {span : ℕ}
    (hnum : num = phi / 2)
    (hspan : span = 6)
    (hS2 : ClosureSignPremise sign) :
    signedPerRung sign num span = -(phi / 2) / 6 := by
  have hs : sign = -1 := hS2
  unfold signedPerRung
  rw [hs, hnum, hspan]
  push_cast
  ring

/-! ## Certificate bundling the honest layers -/

/-- THEOREM-grade certificate for the parts of T2 that are proved. The MODEL premises
`SpanEquidistributionPremise` / `ClosureSignPremise` are NOT fields: they are the irreducible
physical inputs the forcing implications are conditional on. -/
structure TrailingSpanDistributionCert where
  span_six :
    trailingSpan = 6
  numerator_from_T1 :
    LeptonTorsionKernel.terminalFoldKernel = phi / 2
  reconstruct :
    ∀ {n : ℕ}, 0 < n → ∀ (f : Fin n → ℝ), avgShare f * (n : ℝ) = ∑ j, f j
  universality :
    |delta32| * (trailingSpan : ℝ) = phi / 2
  invariant_blind_to_uniformity :
    (∑ i, endpointProfile i) = phi / 2 ∧
      ¬ (∀ i j : Fin 6, endpointProfile i = endpointProfile j)
  perRung_forced :
    ∀ {n : ℕ}, 0 < n → ∀ {sign : ℝ} (f : Fin n → ℝ),
      SpanEquidistributionPremise f → (∑ j, f j) = phi / 2 → n = 6 →
      ClosureSignPremise sign → ∀ i, perRungTorsion sign f i = -(phi / 2) / 6
  delta_matches :
    signedPerRung (-1) (phi / 2) 6 = -(phi / 2) / 6

theorem trailingSpanDistributionCert_holds : Nonempty TrailingSpanDistributionCert :=
  ⟨{ span_six := trailingSpan_eq_six
     numerator_from_T1 := LeptonTorsionKernel.terminalFoldKernel_eq_phi_half
     reconstruct := fun {_n} hn f => reconstruct_total hn f
     universality := universality_invariant
     invariant_blind_to_uniformity := ⟨endpointProfile_sum, endpointProfile_not_uniform⟩
     perRung_forced := fun {_n} hn {_sign} f hS1 htot hspan hS2 i =>
       perRungTorsion_forced hn f hS1 htot hspan hS2 i
     delta_matches := delta32_forced rfl rfl rfl }⟩

end

end TrailingSpanDistribution
end Masses
end IndisputableMonolith
