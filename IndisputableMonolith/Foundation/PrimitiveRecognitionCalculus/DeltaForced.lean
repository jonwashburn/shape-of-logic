/-
  PrimitiveRecognitionCalculus/DeltaForced.lean

  The demarcation predicate: what it means for a type to be δ-forced, and the
  headline split it induces (ℕ, ℤ, ℚ forced; ℝ not).

  Thesis (the ontological reading this module formalizes): an object is PHYSICALLY
  REAL if and only if it is δ-forced. "δ-forced" is given an exact mathematical
  content here: a type is δ-forced when it carries an explicit countable certificate,
  i.e. an injection into ℕ. This is the formal residue of "finitely generated from
  the act of distinction": distinction produces an enumerated carrier, and an
  enumeration is exactly a certificate `X ↪ ℕ`.

  This is deliberately a CERTIFICATE notion, not a cardinality slogan. `Nonempty
  (X ↪ ℕ)` says a witnessing injection EXISTS; for the forced tower we exhibit the
  injection explicitly and choice-free (`Encodable.encode`), so the positive facts
  are constructive, not merely classically true. The negative fact `¬ DeltaForced ℝ`
  is a statement ABOUT the display-tier continuum and may use the classical
  uncountability of ℝ; that is on the non-forced side of the line and does not
  contaminate the forced side.

  Relation to the companion results:
  - Milan's `Distinction, Initiality, and Recognition Quotients` proves the
    cardinality wall (a finite presentation is countable, ℝ is not). This module
    turns that size fact into a predicate and DEFENDS the ontological reading Milan's
    paper explicitly declines to assert, by pinning "forced" to a checkable
    certificate and showing the forced realm is closed under the operations
    distinction performs (pairing, restriction, branch).
  - `PRCCompletenessIndependence` proves completeness is model-theoretically
    independent of the cost/field axioms. `Omniscience.lean` measures HOW MUCH a
    completeness posit costs in omniscience. This module says WHICH objects survive
    the cut.

  No project-local axioms. No sorry. Forced-side facts are `Classical.choice`-free.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Omniscience

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Forced

universe u v

/-- A type is **δ-forced** when it carries an explicit countable certificate: an
injection into ℕ. This is the formal content of "finitely generated, hence
enumerable, from the act of distinction." -/
def DeltaForced (X : Type u) : Prop := Nonempty (X ↪ ℕ)

/-- The ontological reading: **physically real** is, by thesis, exactly δ-forced. The
mathematical content is carried entirely by `DeltaForced`; this name records the
claim that the demarcation line below is the physical one. -/
def PhysicallyReal (X : Type u) : Prop := DeltaForced X

@[simp] theorem physicallyReal_iff_deltaForced (X : Type u) :
    PhysicallyReal X ↔ DeltaForced X := Iff.rfl

/-! ### The forced tower (constructive, choice-free)

Each carrier of the δ tower exhibits an EXPLICIT certificate, built here by hand so
that the positive facts are `Classical.choice`-free. We deliberately do not route
through `Encodable`/`Nat.pair`: Mathlib's `Nat.unpair_pair` (and hence every
`Encodable` injectivity and `Nat.pair_eq_pair`) is proved via `Nat.sqrt` and depends
on `Classical.choice`. The certificates below depend only on `propext` and
`Quot.sound`, matching the δ tower's own constructive status (ℕδ → ℤδ → ℚδ in
`DistinctionNat`/`SignedOrbit`/`RatioOrbit`). -/

/-- Explicit certificate ℤ → ℕ: nonnegatives to evens, negatives to odds. -/
def intToNat : ℤ → ℕ
  | (Int.ofNat k) => 2 * k
  | (Int.negSucc k) => 2 * k + 1

theorem intToNat_inj : Function.Injective intToNat := by
  intro a b h
  cases a with
  | ofNat ka => cases b with
    | ofNat kb => have hk : ka = kb := by have : 2 * ka = 2 * kb := h; omega
                  rw [hk]
    | negSucc kb => exfalso; have : 2 * ka = 2 * kb + 1 := h; omega
  | negSucc ka => cases b with
    | ofNat kb => exfalso; have : 2 * ka + 1 = 2 * kb := h; omega
    | negSucc kb => have hk : ka = kb := by have : 2 * ka + 1 = 2 * kb + 1 := h; omega
                    rw [hk]

/-- The Cantor pairing, defined locally so its reduction is under our control (the
Mathlib `Nat.pair` is the same function but its injectivity lemmas pull
`Classical.choice` through `Nat.sqrt`). -/
def dpair (a b : ℕ) : ℕ := if a < b then b * b + a else a * a + a + b

/-- Injectivity of `dpair`, proved choice-free directly from the `if`-definition. The
two branches tile each square block `[m², (m+1)²)`; the cross cases are arithmetically
impossible and the diagonal cases pin both coordinates. -/
theorem dpair_inj2 {a b c d : ℕ} (h : dpair a b = dpair c d) : a = c ∧ b = d := by
  rcases Nat.lt_or_ge a b with hab | hab <;> rcases Nat.lt_or_ge c d with hcd | hcd
  · -- a < b, c < d : diagonal
    rw [dpair, if_pos hab, dpair, if_pos hcd] at h
    rcases Nat.lt_trichotomy b d with hbd | hbd | hbd
    · exfalso
      have e : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by ring
      have m : (b + 1) * (b + 1) ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
      omega
    · subst hbd; exact ⟨by omega, rfl⟩
    · exfalso
      have e : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by ring
      have m : (d + 1) * (d + 1) ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
      omega
  · -- a < b, c ≥ d : cross, impossible
    exfalso
    rw [dpair, if_pos hab, dpair, if_neg (Nat.not_lt.mpr hcd)] at h
    rcases Nat.lt_trichotomy b c with hbc | hbc | hbc
    · have e : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by ring
      have m : (b + 1) * (b + 1) ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
      omega
    · subst hbc; omega
    · have e : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
      have m : (c + 1) * (c + 1) ≤ b * b := Nat.mul_le_mul (by omega) (by omega)
      omega
  · -- a ≥ b, c < d : cross, impossible
    exfalso
    rw [dpair, if_neg (Nat.not_lt.mpr hab), dpair, if_pos hcd] at h
    rcases Nat.lt_trichotomy a d with had | had | had
    · have e : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
      have m : (a + 1) * (a + 1) ≤ d * d := Nat.mul_le_mul (by omega) (by omega)
      omega
    · subst had; omega
    · have e : (d + 1) * (d + 1) = d * d + 2 * d + 1 := by ring
      have m : (d + 1) * (d + 1) ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
      omega
  · -- a ≥ b, c ≥ d : diagonal
    rw [dpair, if_neg (Nat.not_lt.mpr hab), dpair, if_neg (Nat.not_lt.mpr hcd)] at h
    rcases Nat.lt_trichotomy a c with hac | hac | hac
    · exfalso
      have e : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
      have m : (a + 1) * (a + 1) ≤ c * c := Nat.mul_le_mul (by omega) (by omega)
      omega
    · subst hac; exact ⟨rfl, by omega⟩
    · exfalso
      have e : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by ring
      have m : (c + 1) * (c + 1) ≤ a * a := Nat.mul_le_mul (by omega) (by omega)
      omega

/-- Structure-eta equality for ℚ (definitional proof irrelevance on the `den_nz` and
`reduced` fields), choice-free. -/
theorem rat_eq_of {a b : ℚ} (hn : a.num = b.num) (hd : a.den = b.den) : a = b := by
  obtain ⟨na, da, dnza, reda⟩ := a
  obtain ⟨nb, db, dnzb, redb⟩ := b
  simp only at hn hd
  subst hn; subst hd; rfl

/-- Explicit certificate ℚ → ℕ: pair the (forced) numerator and denominator. -/
def ratToNat (q : ℚ) : ℕ := dpair (intToNat q.num) q.den

theorem ratToNat_inj : Function.Injective ratToNat := by
  intro a b h
  have h2 : dpair (intToNat a.num) a.den = dpair (intToNat b.num) b.den := h
  obtain ⟨hn, hd⟩ := dpair_inj2 h2
  exact rat_eq_of (intToNat_inj hn) hd

/-- ℕ is δ-forced: it is its own certificate. -/
theorem deltaForced_nat : DeltaForced ℕ := ⟨Function.Embedding.refl ℕ⟩

/-- ℤ is δ-forced via the explicit even/odd certificate. Choice-free. -/
theorem deltaForced_int : DeltaForced ℤ := ⟨⟨intToNat, intToNat_inj⟩⟩

/-- ℚ is δ-forced via the explicit paired certificate. This is the top of the forced
tower constructed in the companion algebra paper (ℕδ → ℤδ → ℚδ). Choice-free. -/
theorem deltaForced_rat : DeltaForced ℚ := ⟨⟨ratToNat, ratToNat_inj⟩⟩

/-! ### The continuum is not forced

`ℝ` carries no certificate: a certificate would make ℝ countable, contradicting its
classical uncountability. This is the formal "the continuum is display tier, not
forced." The proof legitimately uses the classical cardinality of ℝ. -/

/-- A δ-forced type is countable (the certificate is an injection into ℕ).
Choice-free. -/
theorem countable_of_deltaForced {X : Type u} (h : DeltaForced X) : Countable X := by
  obtain ⟨e⟩ := h
  exact e.injective.countable

/-- The continuum is **not** δ-forced. A certificate would force `Countable ℝ`, but
ℝ has cardinality `𝔠 > ℵ₀`. -/
theorem not_deltaForced_real : ¬ DeltaForced ℝ := by
  intro h
  have hc : Countable ℝ := countable_of_deltaForced h
  have hle : Cardinal.mk ℝ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hc
  rw [Cardinal.mk_real] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_continuum)

/-! ### The demarcation theorem

The headline split that carries the paper: the entire δ tower is physically real,
and the continuum is not. -/

/-- The forced tower is constructively (choice-free) physically real. Isolated from
the ℝ statement so the positive content carries no `Classical.choice`: this is the
exact formal residue of "the δ tower ℕδ → ℤδ → ℚδ is built, not posited." -/
theorem forcedTower :
    PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ :=
  ⟨deltaForced_nat, deltaForced_int, deltaForced_rat⟩

/-- **Demarcation.** The δ tower (ℕ, ℤ, ℚ) is physically real; the continuum ℝ is
not. The forced-tower conjuncts are choice-free (`forcedTower`); the ℝ conjunct uses
the classical uncountability of ℝ, which is a fact about the display-tier object, not
about the forced side. -/
theorem demarcation :
    PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧ ¬ PhysicallyReal ℝ :=
  ⟨deltaForced_nat, deltaForced_int, deltaForced_rat, not_deltaForced_real⟩

/-! ### Closure of the forced realm

The forced types are closed under the operations distinction actually performs:
forming a pair (product), restricting to a distinguished sub-collection (subtype),
and choosing a branch (sum). These use the `Countable` bridge and are classical;
they describe the algebra of the forced realm, not the primary demarcation, so they
are kept separate from the choice-free core above. -/

/-- δ-forced ↔ countable. The forward direction is choice-free; the backward
direction extracts a certificate from countability and uses choice. -/
theorem deltaForced_iff_countable (X : Type u) : DeltaForced X ↔ Countable X := by
  constructor
  · exact countable_of_deltaForced
  · intro h
    obtain ⟨f, hf⟩ := h.exists_injective_nat'
    exact ⟨⟨f, hf⟩⟩

/-- Pairing two forced collections is forced. -/
theorem deltaForced_prod {X : Type u} {Y : Type v}
    (hX : DeltaForced X) (hY : DeltaForced Y) : DeltaForced (X × Y) := by
  have : Countable X := countable_of_deltaForced hX
  have : Countable Y := countable_of_deltaForced hY
  exact (deltaForced_iff_countable _).mpr inferInstance

/-- Restricting a forced collection to a distinguished sub-collection is forced. -/
theorem deltaForced_subtype {X : Type u} (hX : DeltaForced X) (p : X → Prop) :
    DeltaForced {x // p x} := by
  have : Countable X := countable_of_deltaForced hX
  exact (deltaForced_iff_countable _).mpr inferInstance

/-- Choosing between two forced branches is forced. -/
theorem deltaForced_sum {X : Type u} {Y : Type v}
    (hX : DeltaForced X) (hY : DeltaForced Y) : DeltaForced (X ⊕ Y) := by
  have : Countable X := countable_of_deltaForced hX
  have : Countable Y := countable_of_deltaForced hY
  exact (deltaForced_iff_countable _).mpr inferInstance

end Forced
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
