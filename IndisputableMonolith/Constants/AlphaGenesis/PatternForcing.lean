import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.GapWeight.Formula
import IndisputableMonolith.Foundation.MeasureForcing

/-!
# Alpha Genesis M2: Pattern Forcing

**THE THEOREM.** The φ-pattern `u_t = φᵗ` consumed by the w₈ spectral
projection is not a choice. Any eight-tick ladder pattern with unit base,
constant positive step ratio, and self-similar ratio (`r² = r + 1`, the T6
equation) is exactly `φᵗ`. And the decay envelope `φ⁻ᵏ` inside the spectral
weight is the T9 forced measure itself, term for term.

This discharges discrete choice (ii) of the no-fit proposition (the
"canonical φ-pattern" choice): the pattern is forced by T6 self-similarity
given the T7 carrier, and its conjugate envelope is the unique forced
measure of `Foundation.MeasureForcing`.

## The reciprocity structure

The w₈ machinery consumes two φ-structures:

* the time-domain pattern `φᵗ` (growth display), and
* the spectral decay envelope `φ⁻ᵏ` (weight display).

These are reciprocal displays of ONE object: `pattern · forcedMeasure = 1`
tick by tick (`pattern_mul_forced_measure`). The reciprocity is the ledger's
J-symmetry (`J(x) = J(1/x)`): cost-side and weight-side displays are
conjugate. Neither is an independent input.

STATUS: THEOREM (0 sorry target). No CODATA reference anywhere in this file.
-/

namespace IndisputableMonolith
namespace Constants
namespace AlphaGenesis

noncomputable section

/-- The unique positive root of the self-similarity equation `x² = x + 1`
is φ. (Self-contained; the T6 forcing equation.) -/
theorem pos_root_eq_phi {r : ℝ} (hr : 0 < r) (hsq : r ^ 2 = r + 1) :
    r = Constants.phi := by
  have h5 : (2 * r - 1) ^ 2 = 5 := by nlinarith [hsq]
  have hge : 0 ≤ 2 * r - 1 := by
    by_contra hneg
    push_neg at hneg
    have h2 : (2 * r - 1 + 1) * (1 - (2 * r - 1)) = 1 - (2 * r - 1) ^ 2 := by ring
    have h3 : 0 < (2 * r - 1 + 1) * (1 - (2 * r - 1)) := by
      apply mul_pos
      · linarith
      · linarith
    rw [h2, h5] at h3
    norm_num at h3
  have hsqrt : Real.sqrt 5 = 2 * r - 1 := by
    rw [show (5 : ℝ) = (2 * r - 1) ^ 2 from h5.symm]
    exact Real.sqrt_sq hge
  have hphi : Constants.phi = (1 + Real.sqrt 5) / 2 := rfl
  rw [hphi, hsqrt]
  ring

/-- An **eight-tick ladder pattern**: unit base, constant positive step
ratio, ratio self-similar (the T6 equation `r² = r + 1`). The carrier is the
T7 eight-tick window (indexed by ℕ, consumed at `Fin 8`). -/
structure EightTickLadder where
  /-- The pattern values. -/
  u : ℕ → ℝ
  /-- Unit base: the pattern starts at the identity ratio. -/
  base : u 0 = 1
  /-- The constant step ratio. -/
  ratio : ℝ
  /-- The ratio is positive. -/
  ratio_pos : 0 < ratio
  /-- Constant-ratio recurrence. -/
  step : ∀ n, u (n + 1) = ratio * u n
  /-- Self-similarity (T6): the ratio satisfies `r² = r + 1`. -/
  self_similar : ratio ^ 2 = ratio + 1

namespace EightTickLadder

/-- The ratio of any eight-tick ladder is φ. -/
theorem ratio_eq_phi (L : EightTickLadder) : L.ratio = Constants.phi :=
  pos_root_eq_phi L.ratio_pos L.self_similar

/-- **PATTERN FORCING.** Every eight-tick ladder is the φ-pattern. -/
theorem pattern_forced (L : EightTickLadder) : ∀ n, L.u n = Constants.phi ^ n := by
  intro n
  induction n with
  | zero => simpa using L.base
  | succ k ih =>
      rw [L.step k, ih, L.ratio_eq_phi]
      ring

end EightTickLadder

/-- The canonical ladder (non-vacuity witness). -/
def canonicalLadder : EightTickLadder where
  u := fun n => Constants.phi ^ n
  base := by norm_num
  ratio := Constants.phi
  ratio_pos := Constants.phi_pos
  step := fun n => by ring
  self_similar := Constants.phi_sq_eq

/-- The GapWeight pattern is the forced ladder restricted to the 8-tick
window: `phiPattern t = L.u t` for EVERY admissible ladder L. -/
theorem phiPattern_is_forced (L : EightTickLadder) (t : Fin 8) :
    GapWeight.phiPattern t = L.u t.val := by
  rw [L.pattern_forced]
  rfl

/-- **RECIPROCITY.** The time-domain pattern and the T9 forced measure are
reciprocal displays: `φᵗ · w(t) = 1` at every tick. The growth pattern is
the J-conjugate of the unique forced measure; neither is an independent
input. -/
theorem pattern_mul_forced_measure (t : Fin 8) :
    GapWeight.phiPattern t * Foundation.MeasureForcing.latticeWeight t.val = 1 := by
  show Constants.phi ^ t.val * (1 / Constants.phi) ^ t.val = 1
  rw [one_div, ← mul_pow, mul_inv_cancel₀ Constants.phi_ne_zero, one_pow]

/-- **ENVELOPE IDENTITY.** The decay envelope inside the spectral weight IS
the forced measure: `geometricWeight k = sin²(kπ/8) · latticeWeight k` for
every nonzero mode. The `φ⁻ᵏ` in w₈ is not an α-specific choice; it is the
unique T9 recognition weight. -/
theorem geometricWeight_eq_sin_mul_forced_measure (k : Fin 8) (hk : ¬ k.val = 0) :
    GapWeight.geometricWeight k =
      (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2 *
        Foundation.MeasureForcing.latticeWeight k.val := by
  simp only [GapWeight.geometricWeight, if_neg hk]
  show (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2 * Constants.phi ^ (-(k.val : ℤ)) =
    (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2 * (1 / Constants.phi) ^ k.val
  congr 1
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- **PATTERN FORCING CERTIFICATE.** Bundles the M2 closure:
1. every admissible ladder is `φᵗ` (the pattern is forced, not chosen);
2. the GapWeight pattern is that forced ladder;
3. pattern and forced measure are reciprocal displays;
4. the spectral decay envelope is the forced measure. -/
structure PatternForcingCert where
  deriving Inhabited

@[simp] def PatternForcingCert.verified (_c : PatternForcingCert) : Prop :=
  (∀ (L : EightTickLadder) (n : ℕ), L.u n = Constants.phi ^ n) ∧
  (∀ (L : EightTickLadder) (t : Fin 8), GapWeight.phiPattern t = L.u t.val) ∧
  (∀ t : Fin 8,
    GapWeight.phiPattern t * Foundation.MeasureForcing.latticeWeight t.val = 1) ∧
  (∀ k : Fin 8, ¬ k.val = 0 →
    GapWeight.geometricWeight k =
      (Real.sin ((k.val : ℝ) * Real.pi / 8)) ^ 2 *
        Foundation.MeasureForcing.latticeWeight k.val)

theorem PatternForcingCert.verified_any (c : PatternForcingCert) :
    PatternForcingCert.verified c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L n
    exact L.pattern_forced n
  · intro L t
    exact phiPattern_is_forced L t
  · exact pattern_mul_forced_measure
  · exact geometricWeight_eq_sin_mul_forced_measure

end

end AlphaGenesis
end Constants
end IndisputableMonolith
