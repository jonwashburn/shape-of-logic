import Mathlib

/-!
# GoldenInt: the delta-forced golden ring ℤ[φ]

**The sigma0 (choice-free) re-derivation of the T6 golden-ratio forcing node.**

The existing spine node `Foundation.PhiForcing` proves T6 over `ℝ` with
`Real.sqrt 5`, and its axiom closure is `[propext, Classical.choice, Quot.sound]`:
sigma1 (CHOICE) in the forcing-spectrum grading of `scripts/sigma_audit.py`.
The choice dependency is pure carrier tax. Nothing in "x² = x + 1 has a unique
positive solution and it is φ" needs the continuum.

This module re-derives the same content over the ring ℤ[φ] = ℤ×ℤ with
(a, b) ↦ a + b·φ and multiplication folded through φ² = φ + 1. Everything here
is elementary integer arithmetic: the ring laws are `ring` over ℤ, the integral
domain property reduces via the multiplicative norm N(a+bφ) = a² + ab − b² to
the irrationality of √5, which is proved by strong-induction descent on ℕ.
Positivity of a + b·φ is encoded as a decidable integer predicate on (2a+b, b)
(the exact sign trichotomy of s + b√5), so "φ is the unique positive root" is
stated and proved with no real numbers at all.

**Tactic hygiene (measured, 2026-07-01).** The choice-free toolset was
established by direct axiom probes: `ring` on ℤ, `decide`, `rcases`/`obtain`/
`by_cases`, `Nat.strong_induction_on`, `Int.lt_trichotomy`, and `omega` *when
the goal is a single atom or `False`* all close within `{propext, Quot.sound}`.
Two tools are contaminated and are banned here: full `simp` (its default simp
set reaches choice-tainted Mathlib lemmas; only `simp only [...]` over the
component lemmas below is used) and `omega` on goals with logical structure
(a disjunctive/implicative goal makes `omega` emit a `Classical.choice`-tainted
proof term). Every case split below is therefore an explicit
`Int.lt_trichotomy`/`rcases`, with `omega` used only to close atomic goals.

**Verdict target: sigma0 DELTA_FORCED** — the axiom closure of every theorem
here must be a subset of `{propext, Quot.sound}`. No `Classical.choice`.
Audit with `scripts/sigma_audit.py` or `#print axioms t6_delta_forced`.

The bridge back to the display continuum (`toReal`, `toReal phi = PhiForcing.φ`,
`IsPos x ↔ 0 < toReal x`) lives in `DeltaSpine.GoldenIntReal`, which is honestly
sigma1: the continuum tax is paid exactly once, at the display boundary, not in
the derivation.

Delta Forcing Spectrum program: `Delta_Forcing_Spectrum_20260626.tex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine

/-- The golden ring ℤ[φ]: pairs `(a, b)` representing `a + b·φ`, with the
    multiplication law folded through `φ² = φ + 1`. -/
@[ext]
structure GoldenInt where
  /-- integer part -/
  a : ℤ
  /-- φ-coefficient -/
  b : ℤ
deriving DecidableEq, Repr

namespace GoldenInt

instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
instance : One GoldenInt := ⟨⟨1, 0⟩⟩

/-- φ as an element of ℤ[φ]. -/
def phi : GoldenInt := ⟨0, 1⟩

/-- The conjugate root ψ = 1 − φ. -/
def psi : GoldenInt := ⟨1, -1⟩

instance : Add GoldenInt := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg GoldenInt := ⟨fun x => ⟨-x.a, -x.b⟩⟩

/-- `(a₁ + b₁φ)(a₂ + b₂φ) = (a₁a₂ + b₁b₂) + (a₁b₂ + b₁a₂ + b₁b₂)φ`
    using `φ² = φ + 1`. -/
instance : Mul GoldenInt :=
  ⟨fun x y => ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩⟩

@[simp] theorem zero_a : (0 : GoldenInt).a = 0 := rfl
@[simp] theorem zero_b : (0 : GoldenInt).b = 0 := rfl
@[simp] theorem one_a : (1 : GoldenInt).a = 1 := rfl
@[simp] theorem one_b : (1 : GoldenInt).b = 0 := rfl
@[simp] theorem phi_a : phi.a = 0 := rfl
@[simp] theorem phi_b : phi.b = 1 := rfl
@[simp] theorem psi_a : psi.a = 1 := rfl
@[simp] theorem psi_b : psi.b = -1 := rfl
@[simp] theorem add_a (x y : GoldenInt) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : GoldenInt) : (x + y).b = x.b + y.b := rfl
@[simp] theorem neg_a (x : GoldenInt) : (-x).a = -x.a := rfl
@[simp] theorem neg_b (x : GoldenInt) : (-x).b = -x.b := rfl
@[simp] theorem mul_a (x y : GoldenInt) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : GoldenInt) :
    (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

/-- The component-lemma simp set used everywhere below. Full `simp` is banned
    in this module (choice contamination via the default simp set); every
    rewrite goes through these `rfl`-lemmas plus `ring` over ℤ. -/
macro "golden_simp" : tactic =>
  `(tactic| simp only [zero_a, zero_b, one_a, one_b, phi_a, phi_b, psi_a, psi_b,
      add_a, add_b, neg_a, neg_b, mul_a, mul_b])

/-- ℤ[φ] is a commutative ring. Every law is componentwise `ring` over ℤ,
    which is choice-free. -/
instance : CommRing GoldenInt where
  add_assoc x y z := by ext <;> golden_simp <;> ring
  zero_add x := by ext <;> golden_simp <;> ring
  add_zero x := by ext <;> golden_simp <;> ring
  add_comm x y := by ext <;> golden_simp <;> ring
  mul_assoc x y z := by ext <;> golden_simp <;> ring
  one_mul x := by ext <;> golden_simp <;> ring
  mul_one x := by ext <;> golden_simp <;> ring
  left_distrib x y z := by ext <;> golden_simp <;> ring
  right_distrib x y z := by ext <;> golden_simp <;> ring
  mul_comm x y := by ext <;> golden_simp <;> ring
  zero_mul x := by ext <;> golden_simp <;> ring
  mul_zero x := by ext <;> golden_simp <;> ring
  neg_add_cancel x := by ext <;> golden_simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec

@[simp] theorem sub_a (x y : GoldenInt) : (x - y).a = x.a - y.a := by
  show (x + -y).a = x.a - y.a
  golden_simp
  ring

@[simp] theorem sub_b (x y : GoldenInt) : (x - y).b = x.b - y.b := by
  show (x + -y).b = x.b - y.b
  golden_simp
  ring

/-! ## The multiplicative norm and the integral-domain property -/

/-- The field norm `N(a + bφ) = a² + ab − b²` (the product with the conjugate
    `(a+b) − bφ`). -/
def norm (x : GoldenInt) : ℤ := x.a * x.a + x.a * x.b - x.b * x.b

@[simp] theorem norm_zero : norm 0 = 0 := by decide

/-- The norm is multiplicative. Pure `ring` over ℤ. -/
theorem norm_mul (x y : GoldenInt) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_a, mul_b]
  ring

/-- 5 divides a square only through its root: five-way case split on `x % 5`
    by `rcases` (not by an `omega` disjunction, which would be choice-tainted),
    each residue killed by kernel `decide`. -/
theorem five_dvd_of_five_dvd_sq (x : ℕ) (hx : 5 ∣ x * x) : 5 ∣ x := by
  obtain ⟨c, hc⟩ := hx
  have hmod : x % 5 * (x % 5) % 5 = 0 := by
    rw [← Nat.mul_mod, hc]
    omega
  have hlt : x % 5 < 5 := Nat.mod_lt x (by decide)
  rcases h5 : x % 5 with _ | _ | _ | _ | _ | r
  · exact Nat.dvd_of_mod_eq_zero h5
  · rw [h5] at hmod; exact absurd hmod (by decide)
  · rw [h5] at hmod; exact absurd hmod (by decide)
  · rw [h5] at hmod; exact absurd hmod (by decide)
  · rw [h5] at hmod; exact absurd hmod (by decide)
  · exfalso; rw [h5] at hlt; omega

/-- **Irrationality of √5, ℕ-level, by descent**: no nonzero natural square is
    five times a square. Strong induction; the only tools are `Nat.mul_mod`,
    atomic `omega`, and `ring`-rearrangement, all choice-free. -/
theorem sq_ne_five_sq : ∀ n m : ℕ, m * m = 5 * (n * n) → n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m h
    by_cases hn : n = 0
    · exact hn
    · exfalso
      have h5m : 5 ∣ m := five_dvd_of_five_dvd_sq m ⟨n * n, h⟩
      obtain ⟨k, rfl⟩ := h5m
      have h1 : n * n = 5 * (k * k) := by
        have h' : 5 * (5 * (k * k)) = 5 * (n * n) := by
          calc 5 * (5 * (k * k)) = 5 * k * (5 * k) := by ring
          _ = 5 * (n * n) := h
        omega
      have h5n : 5 ∣ n := five_dvd_of_five_dvd_sq n ⟨k * k, h1⟩
      obtain ⟨j, hj⟩ := h5n
      have h2 : k * k = 5 * (j * j) := by
        have h' : 5 * (5 * (j * j)) = 5 * (k * k) := by
          calc 5 * (5 * (j * j)) = 5 * j * (5 * j) := by ring
          _ = n * n := by rw [hj]
          _ = 5 * (k * k) := h1
        omega
      have hjn : j < n := by omega
      have hj0 : j = 0 := ih j hjn k h2
      omega

/-- Integer form: `s² = 5·b²` forces `b = 0`. -/
theorem int_sq_eq_five_sq {s b : ℤ} (h : s * s = 5 * (b * b)) : b = 0 := by
  have h1 : (s * s).natAbs = (5 * (b * b)).natAbs := by rw [h]
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul] at h1
  have h5 : (5 : ℤ).natAbs = 5 := rfl
  rw [h5] at h1
  exact Int.natAbs_eq_zero.mp (sq_ne_five_sq b.natAbs s.natAbs h1)

/-- The norm vanishes only at 0. This is where the irrationality of √5 does
    its work: `4·N(x) = (2a+b)² − 5b²`. -/
theorem norm_eq_zero_iff {x : GoldenInt} : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have key : (2 * x.a + x.b) * (2 * x.a + x.b) = 5 * (x.b * x.b) := by
      have expand : (2 * x.a + x.b) * (2 * x.a + x.b)
          = 4 * (x.a * x.a + x.a * x.b - x.b * x.b) + 5 * (x.b * x.b) := by ring
      rw [expand, show x.a * x.a + x.a * x.b - x.b * x.b = norm x from rfl, h]
      ring
    have hb : x.b = 0 := int_sq_eq_five_sq key
    have ha : x.a = 0 := by
      have hx : x.a * x.a + x.a * x.b - x.b * x.b = 0 := h
      rw [hb] at hx
      -- hx : x.a * x.a + x.a * 0 - 0 * 0 = 0; `x.a * x.a` is an opaque atom,
      -- the rest is linear, so `omega` stays in its choice-free atomic regime.
      have hnorm : x.a * x.a = 0 := by omega
      -- `Int.mul_eq_zero` is the choice-free route (the generic
      -- `mul_self_eq_zero`/`mul_eq_zero` are Classical.choice-tainted).
      rcases Int.mul_eq_zero.mp hnorm with h' | h' <;> exact h'
    ext
    · rw [ha]; rfl
    · rw [hb]; rfl
  · rintro rfl
    exact norm_zero

/-- **ℤ[φ] is an integral domain** (choice-free, via the multiplicative norm). -/
theorem mul_eq_zero_iff {x y : GoldenInt} : x * y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro h
    have hn : norm x * norm y = 0 := by rw [← norm_mul, h, norm_zero]
    rcases Int.mul_eq_zero.mp hn with h' | h'
    · exact Or.inl (norm_eq_zero_iff.mp h')
    · exact Or.inr (norm_eq_zero_iff.mp h')
  · rintro (rfl | rfl) <;> ext <;> golden_simp <;> ring

/-! ## The golden equation and its exactly-two roots -/

/-- φ satisfies the golden equation `x² = x + 1` — by kernel computation on
    integer literals. -/
theorem phi_sq : phi * phi = phi + 1 := by decide

/-- ψ = 1 − φ also satisfies the golden equation. -/
theorem psi_sq : psi * psi = psi + 1 := by decide

/-- φ ≠ ψ. -/
theorem phi_ne_psi : phi ≠ psi := by decide

/-- The golden polynomial factors: `(x − φ)(x − ψ) = x² − x − 1`. -/
theorem golden_factorization (x : GoldenInt) :
    (x - phi) * (x - psi) = x * x - x - 1 := by
  ext <;> simp only [sub_a, sub_b, mul_a, mul_b, phi_a, phi_b, psi_a, psi_b,
    one_a, one_b] <;> ring

/-- **The golden equation has exactly the two roots φ and ψ in ℤ[φ]**
    (factorization + integral domain; no quadratic formula, no `Real.sqrt`). -/
theorem golden_roots {x : GoldenInt} (h : x * x = x + 1) : x = phi ∨ x = psi := by
  have hfac : (x - phi) * (x - psi) = 0 := by
    rw [golden_factorization, h]
    ring
  rcases mul_eq_zero_iff.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (sub_eq_zero.mp h')

/-! ## Decidable positivity

`a + b·φ = (s + b·√5)/2` with `s = 2a + b`. The sign of `s + b·√5` is decided
by integer comparisons alone, because `√5` is irrational (ties `s² = 5b²` are
impossible for `b ≠ 0`). `IsPos` encodes the exact trichotomy. -/

/-- Sign predicate for `s + t·√5 > 0`, stated entirely in ℤ. The three
    disjuncts are: both components nonnegative and not both zero; `s < 0`
    dominated by `t√5`; `t < 0` dominated by `s`. -/
def PosPair (s t : ℤ) : Prop :=
  (0 ≤ s ∧ 0 ≤ t ∧ (0 < s ∨ 0 < t)) ∨
  (s < 0 ∧ 0 < t ∧ s * s < 5 * (t * t)) ∨
  (0 < s ∧ t < 0 ∧ 5 * (t * t) < s * s)

instance (s t : ℤ) : Decidable (PosPair s t) := by unfold PosPair; infer_instance

/-- Constructive positivity of `a + b·φ = (s + b√5)/2` with `s = 2a + b`. -/
def IsPos (x : GoldenInt) : Prop := PosPair (2 * x.a + x.b) x.b

instance : DecidablePred IsPos := fun x => by unfold IsPos; infer_instance

/-- φ is positive (kernel computation). -/
theorem phi_isPos : IsPos phi := by decide

/-- ψ = 1 − φ is not positive (kernel computation): its real value is
    ≈ −0.618. -/
theorem psi_not_isPos : ¬ IsPos psi := by decide

/-- 0 is not positive (kernel computation). -/
theorem zero_not_isPos : ¬ IsPos (0 : GoldenInt) := by decide

/-- Trichotomy at the pair level: given that the tie `s² = 5t²` forces `t = 0`
    (the irrationality of √5), one of `PosPair s t`, `(s,t) = 0`,
    `PosPair (−s) (−t)` holds. The case split is explicit `Int.lt_trichotomy`
    (choice-free); `omega` only ever closes atomic side goals. -/
theorem posPair_trichotomy {s t : ℤ}
    (hnotie : s * s = 5 * (t * t) → t = 0) :
    PosPair s t ∨ (s = 0 ∧ t = 0) ∨ PosPair (-s) (-t) := by
  unfold PosPair
  have e1 : -s * -s = s * s := by ring
  have e2 : -t * -t = t * t := by ring
  rcases Int.lt_trichotomy s 0 with hs | hs | hs
  · -- s < 0
    rcases Int.lt_trichotomy t 0 with ht | ht | ht
    · -- both negative: −x has both components positive
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩))
    · -- t = 0, s < 0: −x nonneg with 0 < −s
      exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩))
    · -- s < 0 < t: sign decided by s² vs 5t²
      rcases Int.lt_trichotomy (s * s) (5 * (t * t)) with hq | hq | hq
      · exact Or.inl (Or.inr (Or.inl ⟨hs, ht, hq⟩))
      · exfalso; have ht0 := hnotie hq; omega
      · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)))
        rw [e1, e2]; exact hq
  · -- s = 0
    rcases Int.lt_trichotomy t 0 with ht | ht | ht
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, Or.inr (by omega)⟩))
    · exact Or.inr (Or.inl ⟨hs, ht⟩)
    · exact Or.inl (Or.inl ⟨by omega, by omega, Or.inr ht⟩)
  · -- s > 0
    rcases Int.lt_trichotomy t 0 with ht | ht | ht
    · -- 0 < s, t < 0: sign decided by s² vs 5t²
      rcases Int.lt_trichotomy (s * s) (5 * (t * t)) with hq | hq | hq
      · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, ?_⟩)))
        rw [e1, e2]; exact hq
      · exfalso; have ht0 := hnotie hq; omega
      · exact Or.inl (Or.inr (Or.inr ⟨hs, ht, hq⟩))
    · exact Or.inl (Or.inl ⟨by omega, by omega, Or.inl hs⟩)
    · exact Or.inl (Or.inl ⟨by omega, by omega, Or.inl hs⟩)

/-- Exclusivity at the pair level: `s + t√5` cannot be positive in both
    directions. All nine hypothesis cases close with `omega` on `False`
    (atomic; the products `s·s`, `t·t` are opaque atoms). -/
theorem posPair_not_neg {s t : ℤ} (h : PosPair s t) : ¬ PosPair (-s) (-t) := by
  intro hneg
  unfold PosPair at h hneg
  have e1 : -s * -s = s * s := by ring
  have e2 : -t * -t = t * t := by ring
  rw [e1, e2] at hneg
  rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    rcases hneg with ⟨g1, g2, g3 | g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;>
    omega

/-- Exactly one of `IsPos x`, `x = 0`, `IsPos (−x)` holds (the trichotomy
    direction: at least one). The tie case `s² = 5b²` is excluded by the
    descent lemma `int_sq_eq_five_sq`. -/
theorem isPos_trichotomy (x : GoldenInt) : IsPos x ∨ x = 0 ∨ IsPos (-x) := by
  have h := posPair_trichotomy (s := 2 * x.a + x.b) (t := x.b)
    (fun htie => int_sq_eq_five_sq htie)
  rcases h with h | h | h
  · exact Or.inl h
  · refine Or.inr (Or.inl ?_)
    obtain ⟨h1, h2⟩ := h
    have ha : x.a = 0 := by omega
    ext
    · rw [ha]; rfl
    · rw [h2]; rfl
  · refine Or.inr (Or.inr ?_)
    show PosPair (2 * (-x).a + (-x).b) (-x).b
    have harg : 2 * (-x).a + (-x).b = -(2 * x.a + x.b) := by
      rw [neg_a, neg_b]; ring
    rw [harg, show (-x).b = -x.b from rfl]
    exact h

/-- Positivity is exclusive with negativity: `IsPos x` and `IsPos (−x)` cannot
    both hold. -/
theorem isPos_not_neg {x : GoldenInt} (h : IsPos x) : ¬ IsPos (-x) := by
  intro hneg
  have hneg' : PosPair (-(2 * x.a + x.b)) (-x.b) := by
    have harg : 2 * (-x).a + (-x).b = -(2 * x.a + x.b) := by
      rw [neg_a, neg_b]; ring
    have hh := hneg
    unfold IsPos at hh
    rwa [harg, show (-x).b = -x.b from rfl] at hh
  exact posPair_not_neg h hneg'

/-- A positive element is nonzero. -/
theorem isPos_ne_zero {x : GoldenInt} (h : IsPos x) : x ≠ 0 := by
  rintro rfl
  exact zero_not_isPos h

/-! ## The T6 forcing theorem, delta-forced -/

/-- **T6, DELTA-FORCED (sigma0)**: in the golden ring ℤ[φ],

    1. φ satisfies the golden self-similarity equation x² = x + 1;
    2. φ is positive (in the decidable integer sign structure);
    3. the golden equation has exactly the roots φ and ψ = 1 − φ;
    4. φ is the *unique positive* root.

    This is the content of `PhiForcing.phi_unique_self_similar` with the
    continuum stripped away. Axiom closure target: `{propext, Quot.sound}` —
    no `Classical.choice`, no `Real.sqrt`, no `nlinarith` over ℝ. The
    irrationality of √5 (the actual mathematical content of "the golden ratio
    is not rational") is carried by `sq_ne_five_sq`, a strong-induction
    descent over ℕ. -/
theorem t6_delta_forced :
    (phi * phi = phi + 1) ∧
    IsPos phi ∧
    (∀ x : GoldenInt, x * x = x + 1 → x = phi ∨ x = psi) ∧
    (∀ x : GoldenInt, x * x = x + 1 → IsPos x → x = phi) := by
  refine ⟨phi_sq, phi_isPos, fun _ h => golden_roots h, fun x h hp => ?_⟩
  rcases golden_roots h with rfl | rfl
  · rfl
  · exact absurd hp psi_not_isPos

end GoldenInt
end DeltaSpine
end Foundation
end IndisputableMonolith
