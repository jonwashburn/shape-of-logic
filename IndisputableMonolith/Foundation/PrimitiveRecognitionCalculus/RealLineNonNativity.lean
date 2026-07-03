/-
  PrimitiveRecognitionCalculus/RealLineNonNativity.lean

  The Non-Nativity of the Real Line, with teeth.

  Audit context. The certificate layer in `CompletionConservativity.lean` and
  `FiniteCertificateTransfer.lean` uses an arbitrary, prover-chosen `certifies`
  relation with no soundness link to the predicate it certifies. Consequently
  `identity_conservative` makes *every* predicate "conservative," and
  `finite_certificate_transfer` is the identity on its hypotheses. That layer is
  vacuous: it cannot witness that the continuum carries non-native surplus.

  This module supplies the missing content via a cardinality obstruction, which
  is *not* prover-defeatable. The doctrine "the real line is non-native" is made
  precise and TRUE here as: no countable finite-distinction certificate system
  can FAITHFULLY cover ℝ, because faithful (injective) covering forces the
  covered type to be countable, and ℝ is uncountable.

  Honest scope. This is the crude (cardinality) form of the doctrine. It kills
  naive certificate-covering of the continuum itself. It does NOT, by itself,
  kill the Millennium targets whose witness sets are countable (algebraic
  cycles and rational Hodge classes are both countable). For those, cardinality
  gives no obstruction and the genuine obstruction is finer and geometric (for
  Hodge, the diffuse zero-Lelong residual; see
  `IndisputableMonolith.Mathematics.HodgeDiffuseLocalization`). That separation
  is itself a result: it tells you exactly when the doctrine bites by counting
  and when it must descend to structure.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace RealLineNonNativity

/-- A faithful certificate assignment: distinct certified data receive distinct
certificates. This is the minimal soundness a genuine witness must satisfy — a
certificate that determines what it certifies. The vacuous layer drops exactly
this condition. -/
def Faithful {D Cert : Type} (assign : D → Cert) : Prop :=
  Function.Injective assign

/-- A faithful cover into a countable certificate system forces the covered type
to be countable. -/
theorem faithful_cover_into_countable_imp_countable
    {W Cert : Type} [Countable Cert] (assign : W → Cert) (h : Faithful assign) :
    Countable W := by
  have hinj : Function.Injective assign := h
  rw [← Cardinal.mk_le_aleph0_iff]
  have h1 : Cardinal.mk W ≤ Cardinal.mk Cert := Cardinal.mk_le_of_injective hinj
  have h2 : Cardinal.mk Cert ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  exact le_trans h1 h2

/-- **Cardinality obstruction.** A countable certificate system cannot faithfully
cover an uncountable display type: faithful covering would force the display type
to be countable. -/
theorem no_faithful_cover_of_uncountable
    {D Cert : Type} [Countable Cert] (hD : ¬ Countable D) (assign : D → Cert) :
    ¬ Faithful assign :=
  fun hinj => hD (faithful_cover_into_countable_imp_countable assign hinj)

/-- ℝ is uncountable (its cardinality is the continuum, strictly above ℵ₀). -/
theorem real_uncountable : ¬ Countable ℝ := by
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_real]
  exact not_le.mpr Cardinal.aleph0_lt_continuum

/-- **The Non-Nativity of the Real Line (cardinality form).** No countable
finite-distinction certificate system faithfully covers the real line. The
continuum carries surplus that no countable distinction protocol can witness;
ℝ enters only through a completion interface, not from distinction alone. -/
theorem real_not_faithfully_certifiable
    {Cert : Type} [Countable Cert] (assign : ℝ → Cert) :
    ¬ Faithful assign :=
  no_faithful_cover_of_uncountable real_uncountable assign

/-- **Honest refinement: countable witnesses escape the cardinality weapon.** Any
countable witness type admits a faithful certificate assignment into ℕ. So when
the true witnesses are countable — as for algebraic cycles and rational Hodge
classes — cardinality gives no obstruction, and any genuine obstruction must be
finer than counting (for Hodge: the geometric diffuse residual). -/
theorem countable_witness_has_faithful_cover
    {W : Type} [Countable W] : ∃ assign : W → ℕ, Faithful assign := by
  obtain ⟨f, hf⟩ := exists_injective_nat W
  exact ⟨f, hf⟩

/-- The dividing line: a faithful cover into a countable system exists iff the
witness type is countable. This is exactly the boundary between where the
cardinality form of the doctrine bites (uncountable witnesses) and where it does
not (countable witnesses, needing a finer geometric obstruction). -/
theorem faithful_cover_into_countable_iff_countable
    {W : Type} :
    (∃ assign : W → ℕ, Faithful assign) ↔ Countable W := by
  constructor
  · rintro ⟨assign, h⟩
    exact faithful_cover_into_countable_imp_countable assign h
  · intro hW
    exact countable_witness_has_faithful_cover

end RealLineNonNativity
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
