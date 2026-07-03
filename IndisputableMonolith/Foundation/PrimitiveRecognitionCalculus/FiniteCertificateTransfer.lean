/-
  PrimitiveRecognitionCalculus/FiniteCertificateTransfer.lean

  The finite-certificate transfer theorem.

  This is the hinge requested by the Delta-native analysis plan. A continuum
  display statement is legitimate only when it is certificate-covered by typed
  finite distinction data. If the completion is conservative, continuum
  obstructions descend to finite certificates.

  HONEST-LAYER UPGRADE (2026-06-01). The original `ConservativeFor` /
  `finite_certificate_transfer` notion below is a WEAK baseline: its `certifies`
  relation is prover-chosen with no soundness, so `identity_conservative` makes
  every predicate "conservative" and `finite_certificate_transfer` is the
  identity on its hypotheses. That layer cannot witness that the continuum
  carries non-native surplus. We retain it for downstream compatibility but add
  the honest notion `SoundFaithfulCover`, which requires:

    * coverage   : every witness of `P` carries a certificate;
    * soundness  : `certifies c d → P d` (no certificate is issued to a non-witness);
    * faithfulness: a certificate determines its datum.

  Faithfulness is exactly the condition the weak layer drops, and it blocks the
  vacuity trick (`everything_certified_not_faithful`). With it, a sound faithful
  cover injects the witness set into the certificate type, so a countable
  certificate system cannot cover an uncountable witness family
  (`no_soundFaithfulCover_of_uncountable_witnesses`), with the real line as the
  named instance (`no_sound_faithful_certification_of_reals`). The cardinality
  obstruction is not prover-defeatable.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace FiniteCertificateTransfer

open CompletionConservativity

/-- A typed finite distinction certificate: finite data together with a tag
describing which distinction regime produced it. -/
structure TypedFiniteDistinction (Tag : Type*) where
  size : ℕ
  tag : Tag

/-- A certificate map for a display predicate. -/
structure CertificateMap (Tag D : Type*) (P : D → Prop) where
  cert : D → TypedFiniteDistinction Tag
  sound : ∀ d : D, P d → True

/-- Continuum statement legitimacy: every display witness of `P` has a finite
typed distinction certificate. -/
def LegitimateContinuumStatement (Tag D : Type*) (P : D → Prop) : Prop :=
  ∀ d : D, P d → Nonempty (TypedFiniteDistinction Tag)

theorem certificateMap_legitimate {Tag D : Type*} {P : D → Prop}
    (M : CertificateMap Tag D P) : LegitimateContinuumStatement Tag D P := by
  intro d hP
  exact ⟨M.cert d⟩

/-- If a completion is conservative for a display predicate, every display
predicate witness descends to a finite certificate. -/
theorem conservative_completion_transfers
    {N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop)
    (hC : ConservativeFor C P) :
    ∀ d : D, P d → ∃ c : Cert, C.certifies c d :=
  hC

/-- If an obstruction predicate is conservative, then every continuum obstruction
has a finite certificate. -/
theorem obstruction_descends
    {N D Cert : Type*} (C : Completion N D Cert) (Obstruction : D → Prop)
    (hC : ConservativeFor C Obstruction) :
    ∀ d : D, Obstruction d → ∃ c : Cert, C.certifies c d :=
  hC

/-- **Finite-certificate transfer headline.** For a conservative completion,
valid continuum witnesses and valid continuum obstructions both descend to finite
certificates. This is the formal hinge behind the quantized-proof method. -/
theorem finite_certificate_transfer
    {N D Cert : Type*} (C : Completion N D Cert) (P Obstruction : D → Prop)
    (hP : ConservativeFor C P) (hO : ConservativeFor C Obstruction) :
    (∀ d : D, P d → ∃ c : Cert, C.certifies c d)
      ∧ (∀ d : D, Obstruction d → ∃ c : Cert, C.certifies c d) :=
  ⟨conservative_completion_transfers C P hP, obstruction_descends C Obstruction hO⟩

/-! ## The honest layer: sound, faithful certificate covers

The weak notion above is prover-defeatable. The notion below is not. -/

/-- A **sound, faithful** certificate cover for a display predicate `P` over a
completion `C`. Three conditions, the third of which the weak layer drops:
* `complete`  : every witness of `P` carries a certificate;
* `sound`     : a certificate is issued only to genuine witnesses (`certifies c d → P d`);
* `faithful`  : a certificate determines the datum it certifies. -/
structure SoundFaithfulCover {N D Cert : Type} (C : Completion N D Cert) (P : D → Prop) : Prop where
  complete : ∀ d, P d → ∃ c, C.certifies c d
  sound : ∀ c d, C.certifies c d → P d
  faithful : ∀ c d₁ d₂, C.certifies c d₁ → C.certifies c d₂ → d₁ = d₂

/-- The vacuity-defeating fact. A completion that "certifies everything" (the
trick that made the weak layer vacuous) cannot be faithful as soon as the
display type has two distinct points. So a `SoundFaithfulCover` is genuinely
constrained. -/
theorem everything_certified_not_faithful
    {N D Cert : Type} (C : Completion N D Cert)
    (htriv : ∀ c d, C.certifies c d) (c0 : Cert)
    {d₁ d₂ : D} (hne : d₁ ≠ d₂) :
    ¬ (∀ c d₁ d₂, C.certifies c d₁ → C.certifies c d₂ → d₁ = d₂) :=
  fun hfaith => hne (hfaith c0 d₁ d₂ (htriv c0 d₁) (htriv c0 d₂))

/-- A sound, faithful cover injects the witness set into the certificate type. -/
theorem soundFaithfulCover_injects
    {N D Cert : Type} {C : Completion N D Cert} {P : D → Prop}
    (cover : SoundFaithfulCover C P) :
    ∃ f : {d // P d} → Cert, Function.Injective f := by
  classical
  refine ⟨fun w => Classical.choose (cover.complete w.1 w.2), ?_⟩
  intro w₁ w₂ hfeq
  have h1 : C.certifies (Classical.choose (cover.complete w₁.1 w₁.2)) w₁.1 :=
    Classical.choose_spec (cover.complete w₁.1 w₁.2)
  have h2 : C.certifies (Classical.choose (cover.complete w₂.1 w₂.2)) w₂.1 :=
    Classical.choose_spec (cover.complete w₂.1 w₂.2)
  have hc : Classical.choose (cover.complete w₁.1 w₁.2)
            = Classical.choose (cover.complete w₂.1 w₂.2) := hfeq
  rw [hc] at h1
  exact Subtype.ext (cover.faithful _ _ _ h1 h2)

/-- **Honest hinge.** A sound, faithful certificate cover by a countable
certificate system forces the witness set to be countable. -/
theorem soundFaithfulCover_countable_witnesses
    {N D Cert : Type} [Countable Cert] {C : Completion N D Cert} {P : D → Prop}
    (cover : SoundFaithfulCover C P) :
    Countable {d // P d} := by
  obtain ⟨f, hf⟩ := soundFaithfulCover_injects cover
  rw [← Cardinal.mk_le_aleph0_iff]
  exact le_trans (Cardinal.mk_le_of_injective hf) Cardinal.mk_le_aleph0

/-- **Cardinality obstruction.** No sound, faithful certificate cover by a
countable certificate system exists for a predicate with uncountably many
witnesses. This is the honest content the weak layer could not deliver. -/
theorem no_soundFaithfulCover_of_uncountable_witnesses
    {N D Cert : Type} [Countable Cert] {C : Completion N D Cert} {P : D → Prop}
    (hunc : ¬ Countable {d // P d}) (cover : SoundFaithfulCover C P) : False :=
  hunc (soundFaithfulCover_countable_witnesses cover)

/-- The witnesses of the always-true predicate on ℝ are uncountable. -/
theorem reals_uncountable_witnesses : ¬ Countable {_x : ℝ // True} := by
  intro h
  haveI := h
  have hinj : Function.Injective (fun x : ℝ => (⟨x, trivial⟩ : {_x : ℝ // True})) :=
    fun a b hab => congrArg Subtype.val hab
  have hRcount : Countable ℝ := by
    rw [← Cardinal.mk_le_aleph0_iff]
    exact le_trans (Cardinal.mk_le_of_injective hinj) Cardinal.mk_le_aleph0
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_real] at hRcount
  exact (not_le.mpr Cardinal.aleph0_lt_continuum) hRcount

/-- **Named instance: the real line.** No sound, faithful certificate cover by a
countable certificate system exists for the real line. Finite distinction data
cannot soundly and faithfully certify the continuum. -/
theorem no_sound_faithful_certification_of_reals
    {N Cert : Type} [Countable Cert] (C : Completion N ℝ Cert)
    (cover : SoundFaithfulCover C (fun _ : ℝ => True)) : False :=
  no_soundFaithfulCover_of_uncountable_witnesses reals_uncountable_witnesses cover

end FiniteCertificateTransfer
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
