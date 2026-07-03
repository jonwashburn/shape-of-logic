/-
  PrimitiveRecognitionCalculus/Continuum/CharacterRigidityForcing.lean

  Lane: CONSTRUCTIVE CONTINUUM R_δ — calibrated character-rigidity.

  This additive module attacks the rigidity gap that
  `PRCNativeCostUniqueness` leaves OPEN: after setting `g = F + 1` the RCL
  has the d'Alembert form `g(xy) + g(x/y) = 2 g(x) g(y)`, and one-point
  calibration at `2` does not by itself control all prime directions.

  We decompose the missing **calibrated character-rigidity** target into
  small named helper lemmas (each independently true and choice-free) and
  prove the headline single-prime / two-generator rigidity FROM them:
  the set of calibration points of a `PRCRatioCharacter` is closed under
  product, reciprocal and the unit, hence calibration in one prime
  direction rigidifies the whole cyclic subgroup it generates, and the
  generated cost is forced to the canonical PRC J-cost there.

  The genuinely open all-primes statement (one-point calibration at `2`
  forcing global identity) is named honestly as `def target_*`, NOT faked.

  This file cites the committed `PRCJCost` / `PRCNativeCostUniqueness`
  names verbatim (`PRCRatioCharacter`, `costFromCharacter`,
  `doubledTraceValue`, `doubledTraceValue_congr`, `onRatioOrbit`, `two`,
  `RatioOrbit.crossEq`, ...).
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostUniqueness

namespace IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Continuum

open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus
open IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCJCost

/-! ## Calibration predicate -/

/-- A character `χ` is *calibrated at* `q` when its value at `q` is
cross-equivalent to `q` itself, i.e. `χ` acts as the identity character on
the orbit direction `q`.  Calibration at `two` is the single-point datum the
PRC cost hypotheses actually carry. -/
def CharacterCalibratedAt (χ : RatioOrbit → RatioOrbit) (q : RatioOrbit) : Prop :=
  RatioOrbit.crossEq (χ q) q

/-! ## Helper lemmas: rational displays of a ratio character -/

/-- Multiplicativity of a `PRCRatioCharacter` on the verifier rational display. -/
theorem character_mul_toRat {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) (x y : RatioOrbit) :
    (χ (RatioOrbit.mul x y)).toRat = (χ x).toRat * (χ y).toRat := by
  have h := hχ.multiplicative x y
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [h, RatioOrbit.mul_toRat]

/-- The unit normalization of a `PRCRatioCharacter` on the rational display. -/
theorem character_one_toRat {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) :
    (χ RatioOrbit.one).toRat = 1 := by
  have h := hχ.unit
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [h, RatioOrbit.one_toRat]

/-- Reciprocal symmetry of a `PRCRatioCharacter` on the rational display. -/
theorem character_recip_toRat {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) (x : RatioOrbit) :
    (χ (RatioOrbit.recip x)).toRat = (χ x).toRat⁻¹ := by
  have h := hχ.reciprocal x
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h
  rw [h, RatioOrbit.recip_toRat]

/-! ## Helper lemmas: the calibration set is a subgroup -/

/-- The unit orbit is always a calibration point of a `PRCRatioCharacter`. -/
theorem calibrated_one {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) :
    CharacterCalibratedAt χ RatioOrbit.one :=
  hχ.unit

/-- Calibration is closed under products: if `χ` is the identity on `x` and
on `y`, multiplicativity forces it to be the identity on `x·y`. -/
theorem calibrated_mul {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {x y : RatioOrbit}
    (hx : CharacterCalibratedAt χ x) (hy : CharacterCalibratedAt χ y) :
    CharacterCalibratedAt χ (RatioOrbit.mul x y) := by
  unfold CharacterCalibratedAt at hx hy ⊢
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hx hy ⊢
  rw [character_mul_toRat hχ, RatioOrbit.mul_toRat, hx, hy]

/-- Calibration is closed under reciprocals. -/
theorem calibrated_recip {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {x : RatioOrbit}
    (hx : CharacterCalibratedAt χ x) :
    CharacterCalibratedAt χ (RatioOrbit.recip x) := by
  unfold CharacterCalibratedAt at hx ⊢
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hx ⊢
  rw [character_recip_toRat hχ, RatioOrbit.recip_toRat, hx]

/-- Two-generator / square case: calibration at `p` propagates to `p·p`. -/
theorem calibrated_square {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {p : RatioOrbit}
    (hp : CharacterCalibratedAt χ p) :
    CharacterCalibratedAt χ (RatioOrbit.mul p p) :=
  calibrated_mul hχ hp hp

/-! ## Helper lemmas: cost / trace rigidity from calibration -/

/-- The canonical PRC cost respects cross-equivalence of inputs. -/
theorem onRatioOrbit_crossEq {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    RatioOrbit.crossEq (onRatioOrbit a) (onRatioOrbit b) := by
  rw [RatioOrbit.crossEq_iff_toRat_eq] at h ⊢
  rw [onRatioOrbit_toRat, onRatioOrbit_toRat, h]

/-- The d'Alembert trace `χ(p) + χ(p)⁻¹` of a calibrated character collapses
to the identity trace `p + p⁻¹` on a calibration point. -/
theorem character_trace_rigid {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {p : RatioOrbit}
    (hp : CharacterCalibratedAt χ p) :
    RatioOrbit.crossEq
      (RatioOrbit.add (χ p) (RatioOrbit.recip (χ p)))
      (RatioOrbit.add p (RatioOrbit.recip p)) := by
  unfold CharacterCalibratedAt at hp
  rw [RatioOrbit.crossEq_iff_toRat_eq] at hp ⊢
  rw [RatioOrbit.add_toRat, RatioOrbit.add_toRat, RatioOrbit.recip_toRat,
    RatioOrbit.recip_toRat, hp]

/-- The cost generated by a calibrated character equals the canonical PRC
J-cost on a calibration point: `costFromCharacter χ p ≈ onRatioOrbit p`. -/
theorem costFromCharacter_rigid {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {p : RatioOrbit}
    (hp : CharacterCalibratedAt χ p) :
    RatioOrbit.crossEq (costFromCharacter χ p) (onRatioOrbit p) :=
  onRatioOrbit_crossEq hp

/-- The doubled d'Alembert trace `2(F+1)` of the generated cost is rigidified
to the canonical doubled trace on a calibration point. -/
theorem doubledTrace_character_rigid {χ : RatioOrbit → RatioOrbit}
    (hχ : PRCRatioCharacter χ) {p : RatioOrbit}
    (hp : CharacterCalibratedAt χ p) :
    RatioOrbit.crossEq
      (doubledTraceValue (costFromCharacter χ p))
      (doubledTraceValue (onRatioOrbit p)) :=
  doubledTraceValue_congr (costFromCharacter_rigid hχ hp)

/-! ## Headline: single-prime / two-generator calibrated rigidity -/

/-- **Calibrated character-rigidity (single prime direction).**

A `PRCRatioCharacter χ` that is calibrated at a prime direction `p`
(`χ p ≈ p`) is rigidified there: it is forced to remain the identity
character on `p·p` and on `p⁻¹` (so on the whole cyclic subgroup `p`
generates), and the cost it generates is forced to the canonical PRC
J-cost `onRatioOrbit p`.  This is exactly the rigidity that calibrated
multiplicativity supplies; the global all-primes step requires the
separate `target_*` below. -/
theorem prime_calibration_forces_identity_on_direction
    {χ : RatioOrbit → RatioOrbit} (hχ : PRCRatioCharacter χ)
    {p : RatioOrbit} (hcalib : CharacterCalibratedAt χ p) :
    CharacterCalibratedAt χ (RatioOrbit.mul p p)
      ∧ CharacterCalibratedAt χ (RatioOrbit.recip p)
      ∧ RatioOrbit.crossEq (costFromCharacter χ p) (onRatioOrbit p) :=
  ⟨calibrated_mul hχ hcalib hcalib,
   calibrated_recip hχ hcalib,
   costFromCharacter_rigid hχ hcalib⟩

/-! ## The genuinely open all-primes target (named, not faked) -/

/-- **Open target.**  One-point calibration at `two` forces global identity:
every `PRCRatioCharacter` that is calibrated only at the distinguished axis
`two` is in fact calibrated (cross-equivalent to the identity character) at
every nonzero ratio orbit.  This is the all-prime-directions statement that
`PRCNativeCostUniqueness` leaves OPEN; the single-prime lemma above provides
the per-direction rigidity, but propagating one-point calibration across
independent prime directions is the remaining content.  Stated honestly as a
`Prop`, not proved here. -/
def target_OnePointCalibrationForcesGlobalIdentity : Prop :=
  ∀ χ : RatioOrbit → RatioOrbit, PRCRatioCharacter χ →
    CharacterCalibratedAt χ two →
      ∀ q : RatioOrbit, q.toRat ≠ 0 → CharacterCalibratedAt χ q

end IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Continuum
