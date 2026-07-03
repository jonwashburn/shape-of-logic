import Mathlib
import IndisputableMonolith.Cost

/-!
# ECDLP Watch Surface

This module defines a small, explicit surface for auditing elliptic-curve
discrete logarithm claims. It is not an attack module.

The goal is to make the ordinary mathematical problem precise before testing
any RS candidate invariant: a finite carrier `ZMod p`, a short Weierstrass
curve, points including infinity, the chord-tangent group operation, scalar
multiplication, and an ECDLP solution predicate.
-/

namespace IndisputableMonolith
namespace Cryptography
namespace ECDLPWatch

open scoped Pointwise

/-- Short Weierstrass curve over `ZMod p`: `y^2 = x^3 + a*x + b`. -/
structure ShortWeierstrassCurve (p : ℕ) where
  a : ZMod p
  b : ZMod p

/-- Discriminant nonvanishing condition for `y^2 = x^3 + ax + b`. -/
def nonsingular {p : ℕ} (E : ShortWeierstrassCurve p) : Prop :=
  (4 : ZMod p) * E.a ^ 3 + (27 : ZMod p) * E.b ^ 2 ≠ 0

/-- Projective point surface specialized to a short Weierstrass equation. -/
inductive ECPoint (p : ℕ) where
  | infinity : ECPoint p
  | affine : ZMod p → ZMod p → ECPoint p
deriving DecidableEq, Repr

/-- The curve equation, with infinity admitted as the identity point. -/
def onCurve {p : ℕ} (E : ShortWeierstrassCurve p) : ECPoint p → Prop
  | ECPoint.infinity => True
  | ECPoint.affine x y => y ^ 2 = x ^ 3 + E.a * x + E.b

/-- Negation in the elliptic-curve group law. -/
def neg {p : ℕ} : ECPoint p → ECPoint p
  | ECPoint.infinity => ECPoint.infinity
  | ECPoint.affine x y => ECPoint.affine x (-y)

instance {p : ℕ} : Neg (ECPoint p) where
  neg := neg

/-- Chord slope for two distinct affine x-coordinates. -/
def chordSlope {p : ℕ} (x₁ y₁ x₂ y₂ : ZMod p) : ZMod p :=
  (y₂ - y₁) * (x₂ - x₁)⁻¹

/-- Tangent slope for point doubling. -/
def tangentSlope {p : ℕ} (E : ShortWeierstrassCurve p) (x y : ZMod p) : ZMod p :=
  ((3 : ZMod p) * x ^ 2 + E.a) * ((2 : ZMod p) * y)⁻¹

/-- Third point obtained from the usual slope formula. -/
def slopeAddPoint {p : ℕ} (m x₁ y₁ x₂ : ZMod p) : ECPoint p :=
  let x₃ := m ^ 2 - x₁ - x₂
  let y₃ := m * (x₁ - x₃) - y₁
  ECPoint.affine x₃ y₃

/-- Total chord-tangent addition formula. The usual prime-field side
conditions are carried separately by benchmark code and hypotheses. -/
def pointAdd {p : ℕ} (E : ShortWeierstrassCurve p) : ECPoint p → ECPoint p → ECPoint p
  | ECPoint.infinity, Q => Q
  | P, ECPoint.infinity => P
  | ECPoint.affine x₁ y₁, ECPoint.affine x₂ y₂ =>
      if _hx : x₁ = x₂ then
        if _hy : y₁ + y₂ = 0 then
          ECPoint.infinity
        else
          slopeAddPoint (tangentSlope E x₁ y₁) x₁ y₁ x₁
      else
        slopeAddPoint (chordSlope x₁ y₁ x₂ y₂) x₁ y₁ x₂

/-- Scalar multiplication by repeated addition. This is the reference
specification, not an efficient implementation. -/
def scalarMul {p : ℕ} (E : ShortWeierstrassCurve p) : ℕ → ECPoint p → ECPoint p
  | 0, _P => ECPoint.infinity
  | n + 1, P => pointAdd E P (scalarMul E n P)

/-- Curve-family tag used by the watch harness. -/
inductive CurveFamily where
  | toy
  | anomalous
  | supersingular
  | smallEmbeddingDegree
  | ordinaryPrimeOrder
  | standardLike
deriving DecidableEq, Repr

/-- Minimal ECDLP instance: recover `k` from `Q = kP`. -/
structure ECDLPInstance (p : ℕ) where
  curve : ShortWeierstrassCurve p
  base : ECPoint p
  target : ECPoint p
  order : ℕ
  cofactor : ℕ
  family : CurveFamily
  curve_ok : nonsingular curve
  base_on_curve : onCurve curve base
  target_on_curve : onCurve curve target

/-- Candidate solution predicate for the elliptic-curve discrete log problem. -/
def isSolution {p : ℕ} (inst : ECDLPInstance p) (k : ℕ) : Prop :=
  k < inst.order ∧ scalarMul inst.curve k inst.base = inst.target

/-- Public data available to an adversary. This structure exists to keep later
RS invariants honest: they may depend only on these fields. -/
structure PublicECDLPData (p : ℕ) where
  curve : ShortWeierstrassCurve p
  base : ECPoint p
  target : ECPoint p
  order : ℕ
  cofactor : ℕ
  family : CurveFamily

def ECDLPInstance.publicData {p : ℕ} (inst : ECDLPInstance p) : PublicECDLPData p where
  curve := inst.curve
  base := inst.base
  target := inst.target
  order := inst.order
  cofactor := inst.cofactor
  family := inst.family

/-- A watch invariant is admissible only if it is computed from public data. -/
structure PublicInvariant where
  score : ∀ {p : ℕ}, PublicECDLPData p → ℝ

/-- Known weak-curve classes must be separated from any standard-curve claim. -/
def isKnownWeakFamily : CurveFamily → Prop
  | CurveFamily.anomalous => True
  | CurveFamily.supersingular => True
  | CurveFamily.smallEmbeddingDegree => True
  | _ => False

/-- Watch predicate: a candidate invariant is being tested only on public data
and against an explicitly tagged curve family. This carries no security claim. -/
structure InvariantWatchRecord (I : PublicInvariant) where
  family : CurveFamily
  weak_family_tagged : isKnownWeakFamily family ∨ ¬ isKnownWeakFamily family

end ECDLPWatch
end Cryptography
end IndisputableMonolith
