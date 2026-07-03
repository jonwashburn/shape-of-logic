import IndisputableMonolith.DeltaKernel.Syntax
import IndisputableMonolith.DeltaKernel.Ledger
import IndisputableMonolith.DeltaKernel.Check
import IndisputableMonolith.DeltaKernel.Semantics

/-!
# δ-Kernel: Soundness in the Canonical Model

This is the kernel certifying itself. Every derivation the checker accepts is
true in the canonical model ℕδ, and the ledger the checker returns is an HONEST
upper bound on the metatheoretic strength the truth of the conclusion actually
requires:

- If the ledger posts no EM, the conclusion is proved WITHOUT classical excluded
  middle in the metatheory (constructively).
- If the ledger posts no LPO, without the limited principle of omniscience.
- If the ledger posts no MP, without Markov's principle.

The central theorem `sound_cond` is CONDITIONAL: each posit's metatheoretic
principle is supplied only when the ledger actually posted it (gated on the
Boolean flags). Two corollaries fall out by instantiating the gates:

- `sound_forced`: a FORCED derivation (empty ledger) is true with NONE of the
  three principles. The gates are discharged vacuously (`false = true`), so the
  proof term never touches EM/LPO/MP or `Classical.choice`. `#print axioms
  sound_forced` is the kernel's own σ0/DELTA_FORCED self-audit.
- `sound_classical`: ANY accepted derivation is true, supplying all three
  principles from `Classical`. This is the "run the whole thing over classical
  metatheory" reading, and it is where `Classical.choice` enters, by design and
  by ledger.

The tier flag (`indFull`) is orthogonal to soundness: FULL induction is sound in
ℕδ regardless (the model genuinely satisfies the induction schema). The flag
exists to MEASURE which theorems used it, not to gate their truth. That is why
soundness does not branch on `indFull`.

No Mathlib: only the kernel's own modules and core Lean. This keeps the
choice-free claim about `sound_forced` maximally trustworthy.
-/

namespace IndisputableMonolith
namespace DeltaKernel

open DTerm DFormula

/-! ## Metatheoretic principles, as plain host Props

Each is the semantic content of one posit rule, stated over the canonical model.
They are supplied to `sound_cond` only when the ledger flags them. -/

/-- Metatheoretic excluded middle. Content of the EM posit. -/
def MetaEM : Prop := ∀ (P : Prop), P ∨ ¬P

/-- Metatheoretic limited principle of omniscience (arithmetical form). Content
of the LPO posit. -/
def MetaLPO : Prop :=
  ∀ (P : Nat → Prop), (∀ n, P n ∨ ¬ P n) → (∃ n, P n) ∨ (∀ n, ¬ P n)

/-- Metatheoretic Markov's principle over a pointwise-decidable predicate.
Content of the MP posit. -/
def MetaMP : Prop :=
  ∀ (P : Nat → Prop), (∀ n, P n ∨ ¬ P n) → ¬¬(∃ n, P n) → ∃ n, P n

/-! ## Quantifier-free satisfaction is decidable (constructively)

The MP posit is restricted to quantifier-free matrices precisely so that its
matrix is pointwise decidable WITHOUT any omniscience. This lemma discharges the
pointwise-decidability premise of `MetaMP` from the checker's `isQF` guard, and
it is choice-free (structural recursion + `Nat.decEq`). -/

theorem satQF_dec : ∀ (φ : DFormula), φ.isQF = true → ∀ ρ : Env,
    DFormula.sat ρ φ ∨ ¬ DFormula.sat ρ φ
  | .eq t s, _, ρ => by
      simp only [DFormula.sat]
      cases Nat.decEq (t.eval ρ) (s.eval ρ) with
      | isFalse h => exact Or.inr h
      | isTrue h => exact Or.inl h
  | .fls, _, _ => Or.inr (fun h => h)
  | .conj a b, hqf, ρ => by
      have hab : a.isQF = true ∧ b.isQF = true := by
        simpa [DFormula.isQF, Bool.and_eq_true] using hqf
      have ha := satQF_dec a hab.1 ρ
      have hb := satQF_dec b hab.2 ρ
      simp only [DFormula.sat]
      rcases ha with ha | ha
      · rcases hb with hb | hb
        · exact Or.inl ⟨ha, hb⟩
        · exact Or.inr (fun h => hb h.2)
      · exact Or.inr (fun h => ha h.1)
  | .disj a b, hqf, ρ => by
      have hab : a.isQF = true ∧ b.isQF = true := by
        simpa [DFormula.isQF, Bool.and_eq_true] using hqf
      have ha := satQF_dec a hab.1 ρ
      have hb := satQF_dec b hab.2 ρ
      simp only [DFormula.sat]
      rcases ha with ha | ha
      · exact Or.inl (Or.inl ha)
      · rcases hb with hb | hb
        · exact Or.inl (Or.inr hb)
        · exact Or.inr (fun h => h.elim ha hb)
  | .impl a b, hqf, ρ => by
      have hab : a.isQF = true ∧ b.isQF = true := by
        simpa [DFormula.isQF, Bool.and_eq_true] using hqf
      have ha := satQF_dec a hab.1 ρ
      have hb := satQF_dec b hab.2 ρ
      simp only [DFormula.sat]
      rcases hb with hb | hb
      · exact Or.inl (fun _ => hb)
      · rcases ha with ha | ha
        · exact Or.inr (fun f => hb (f ha))
        · exact Or.inl (fun h => absurd h ha)
  | .all _, hqf, _ => by simp [DFormula.isQF] at hqf
  | .ex _, hqf, _ => by simp [DFormula.isQF] at hqf

/-! ## Context satisfaction -/

/-- All hypotheses of the context hold under `ρ`. -/
def CtxSat (ρ : Env) (Γ : Ctx) : Prop := ∀ φ, φ ∈ Γ → DFormula.sat ρ φ

theorem CtxSat.cons {ρ : Env} {Γ : Ctx} {ψ : DFormula}
    (hψ : DFormula.sat ρ ψ) (hΓ : CtxSat ρ Γ) : CtxSat ρ (ψ :: Γ) := by
  intro φ hmem
  rcases List.mem_cons.mp hmem with h | h
  · exact h ▸ hψ
  · exact hΓ φ h

theorem CtxSat.head {ρ : Env} {Γ : Ctx} {ψ : DFormula}
    (h : CtxSat ρ (ψ :: Γ)) : DFormula.sat ρ ψ :=
  h ψ (List.mem_cons_self ..)

theorem CtxSat.tail {ρ : Env} {Γ : Ctx} {ψ : DFormula}
    (h : CtxSat ρ (ψ :: Γ)) : CtxSat ρ Γ :=
  fun φ hmem => h φ (List.mem_cons_of_mem _ hmem)

/-- Weakening the context by one fresh distinction variable: the lifted context
holds under the extended environment. Used for ∀-intro and ∃-elim. -/
theorem CtxSat.mapLift {ρ : Env} {Γ : Ctx} (n : Nat) (hΓ : CtxSat ρ Γ) :
    CtxSat (Env.cons n ρ) (Γ.map (DFormula.lift 1 0)) := by
  intro φ hmem
  rcases List.mem_map.mp hmem with ⟨ψ, hψmem, rfl⟩
  exact (DFormula.sat_lift0 ψ n ρ).mpr (hΓ ψ hψmem)

/-! ## The ledger gate

`Gated O` supplies each metatheoretic principle exactly when the ledger `O`
posts the matching posit. The whole soundness proof threads a single `Gated O`
and projects it onto sub-ledgers via the posit-monotonicity lemmas; that
projection is the semantic counterpart of "a posit consumed by a premise is
consumed by the conclusion." -/

/-- The metatheoretic principles gated by a ledger's posit flags. -/
def Gated (O : Ledger) : Prop :=
  (O.em = true → MetaEM) ∧ (O.lpo = true → MetaLPO) ∧ (O.mp = true → MetaMP)

theorem Gated.union_left {a b : Ledger} (h : Gated (a.union b)) : Gated a :=
  ⟨fun hem => h.1 (Ledger.em_left hem),
   fun hlpo => h.2.1 (Ledger.lpo_left hlpo),
   fun hmp => h.2.2 (Ledger.mp_left hmp)⟩

theorem Gated.union_right {a b : Ledger} (h : Gated (a.union b)) : Gated b :=
  ⟨fun hem => h.1 (Ledger.em_right hem),
   fun hlpo => h.2.1 (Ledger.lpo_right hlpo),
   fun hmp => h.2.2 (Ledger.mp_right hmp)⟩

/-- The empty ledger gates nothing, so `Gated Ledger.empty` holds unconditionally
(the posit flags are all `false`, so every antecedent is `false = true`). This is
why the FORCED corollary needs none of the three principles. -/
theorem Gated.empty : Gated Ledger.empty :=
  ⟨fun h => by simp [Ledger.empty] at h,
   fun h => by simp [Ledger.empty] at h,
   fun h => by simp [Ledger.empty] at h⟩

/-! ## A context hypothesis is satisfied

Small structural fact: an index into the context names a member. Proved by
structural recursion so the FORCED corollary stays choice-free. -/

private theorem mem_of_getElem? {α : Type _} :
    ∀ {l : List α} {i : Nat} {a : α}, l[i]? = some a → a ∈ l
  | [], _, _, h => by simp at h
  | x :: xs, 0, a, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
  | _ :: xs, i + 1, a, h => by
      simp only [List.getElem?_cons_succ] at h
      exact List.mem_cons_of_mem _ (mem_of_getElem? h)

/-! ## Conditional soundness

The kernel certifies itself. `sound_cond` is proved by induction on the
derivation TREE (`Deriv` is data), with the context, conclusion, ledger, and
environment universally quantified so the induction hypothesis applies to every
sub-derivation in whatever context the checker recursed into. The `Gated O`
hypothesis is threaded down to each premise via the posit-monotonicity lemmas:
a posit consumed by a premise is consumed by the conclusion, so the semantic
principle it licenses is available to the premise too. -/

theorem sound_cond : ∀ (d : Deriv) (Γ : Ctx) (φ : DFormula) (O : Ledger),
    check Γ d = some (φ, O) → Gated O → ∀ ρ : Env, CtxSat ρ Γ → DFormula.sat ρ φ := by
  intro d
  induction d with
  | hyp i =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hg : Γ[i]? with
      | none => simp [hg] at hchk
      | some ψ =>
          simp only [hg, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨hφ, _⟩ := hchk
          subst hφ
          exact hΓ ψ (mem_of_getElem? hg)
  | eqRefl t =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      rfl
  | eqSubst hole t s dEq dT ihEq ihT =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hdE : check Γ dEq with
      | none => simp [hdE] at hchk
      | some cpE =>
          obtain ⟨cEq, o₁⟩ := cpE
          cases hdT : check Γ dT with
          | none => simp [hdE, hdT] at hchk
          | some cpT =>
              obtain ⟨cT, o₂⟩ := cpT
              simp only [hdE, hdT] at hchk
              split at hchk
              · rename_i h1
                split at hchk
                · rename_i h2
                  simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                  obtain ⟨hc, hO⟩ := hchk
                  subst hc; subst hO
                  have HE := ihEq Γ cEq o₁ hdE (Gated.union_left hG) ρ hΓ
                  have HT := ihT Γ cT o₂ hdT (Gated.union_right hG) ρ hΓ
                  rw [h1] at HE
                  rw [h2] at HT
                  have hts : t.eval ρ = s.eval ρ := HE
                  rw [DFormula.sat_subst0] at HT
                  rw [DFormula.sat_subst0]
                  rw [← hts]
                  exact HT
                · nomatch hchk
              · nomatch hchk
  | succNeZero t =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      simp only [DFormula.sat, DFormula.neg, DTerm.eval]
      omega
  | succInj d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | eq a b =>
              cases a with
              | succ ta =>
                  cases b with
                  | succ tb =>
                      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
                      obtain ⟨hc, hO⟩ := hchk
                      subst hc; subst hO
                      have H := ih Γ (DFormula.eq (DTerm.succ ta) (DTerm.succ tb)) o hd hG ρ hΓ
                      simp only [DFormula.sat, DTerm.eval] at H ⊢
                      omega
                  | var _ => simp [hd] at hchk
                  | zero => simp [hd] at hchk
                  | add _ _ => simp [hd] at hchk
                  | mul _ _ => simp [hd] at hchk
              | var _ => simp [hd] at hchk
              | zero => simp [hd] at hchk
              | add _ _ => simp [hd] at hchk
              | mul _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | addZero t =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      simp only [DFormula.sat, DTerm.eval]
      omega
  | addSucc t s =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      simp only [DFormula.sat, DTerm.eval]
      omega
  | mulZero t =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      simp [DFormula.sat, DTerm.eval]
  | mulSucc t s =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, _⟩ := hchk
      subst hc
      simp only [DFormula.sat, DTerm.eval]
      exact Nat.mul_succ (t.eval ρ) (s.eval ρ)
  | ind hole d0 dS ih0 ihS =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd0 : check Γ d0 with
      | none => simp [hd0] at hchk
      | some cp0 =>
          obtain ⟨c0, o₁⟩ := cp0
          cases hdS : check Γ dS with
          | none => simp [hd0, hdS] at hchk
          | some cpS =>
              obtain ⟨cS, o₂⟩ := cpS
              simp only [hd0, hdS] at hchk
              split at hchk
              · rename_i hc0
                split at hchk
                · rename_i hcS
                  simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                  obtain ⟨hc, hO⟩ := hchk
                  subst hc
                  have hbase : Gated (o₁.union o₂) := by
                    split at hO
                    · subst hO; exact hG
                    · subst hO; exact Gated.union_left hG
                  have H0 := ih0 Γ c0 o₁ hd0 (Gated.union_left hbase) ρ hΓ
                  have HS := ihS Γ cS o₂ hdS (Gated.union_right hbase) ρ hΓ
                  rw [hc0] at H0
                  rw [hcS] at HS
                  have H0' := (DFormula.sat_subst0 hole DTerm.zero ρ).mp H0
                  simp only [DFormula.sat] at HS
                  simp only [DFormula.sat]
                  intro n
                  induction n with
                  | zero => exact H0'
                  | succ k ihk => exact (DFormula.sat_stepSucc hole k ρ).mp (HS k ihk)
                · nomatch hchk
              · nomatch hchk
  | implIntro hole d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check (hole :: Γ) d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨hc, hO⟩ := hchk
          subst hc; subst hO
          simp only [DFormula.sat]
          intro hhole
          exact ih (hole :: Γ) c o hd hG ρ (CtxSat.cons hhole hΓ)
  | implElim d1 d2 ih1 ih2 =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd1 : check Γ d1 with
      | none => simp [hd1] at hchk
      | some cp1 =>
          obtain ⟨c1, o₁⟩ := cp1
          cases hd2 : check Γ d2 with
          | none => simp [hd1, hd2] at hchk
          | some cp2 =>
              obtain ⟨c2, o₂⟩ := cp2
              cases c1 with
              | impl a b =>
                  simp only [hd1, hd2] at hchk
                  split at hchk
                  · rename_i hcond
                    simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                    obtain ⟨hb, hO⟩ := hchk
                    subst hb; subst hO
                    have H1 := ih1 Γ (DFormula.impl a b) o₁ hd1 (Gated.union_left hG) ρ hΓ
                    have H2 := ih2 Γ c2 o₂ hd2 (Gated.union_right hG) ρ hΓ
                    rw [hcond] at H2
                    exact H1 H2
                  · nomatch hchk
              | eq _ _ => simp [hd1, hd2] at hchk
              | fls => simp [hd1, hd2] at hchk
              | conj _ _ => simp [hd1, hd2] at hchk
              | disj _ _ => simp [hd1, hd2] at hchk
              | all _ => simp [hd1, hd2] at hchk
              | ex _ => simp [hd1, hd2] at hchk
  | conjIntro d1 d2 ih1 ih2 =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd1 : check Γ d1 with
      | none => simp [hd1] at hchk
      | some cp1 =>
          obtain ⟨c1, o₁⟩ := cp1
          cases hd2 : check Γ d2 with
          | none => simp [hd1, hd2] at hchk
          | some cp2 =>
              obtain ⟨c2, o₂⟩ := cp2
              simp only [hd1, hd2, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨hc, hO⟩ := hchk
              subst hc; subst hO
              have H1 := ih1 Γ c1 o₁ hd1 (Gated.union_left hG) ρ hΓ
              have H2 := ih2 Γ c2 o₂ hd2 (Gated.union_right hG) ρ hΓ
              exact ⟨H1, H2⟩
  | conjElim1 d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | conj a b =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨hc, hO⟩ := hchk
              subst hc; subst hO
              have H := ih Γ (DFormula.conj a b) o hd hG ρ hΓ
              exact H.1
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | conjElim2 d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | conj a b =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨hc, hO⟩ := hchk
              subst hc; subst hO
              have H := ih Γ (DFormula.conj a b) o hd hG ρ hΓ
              exact H.2
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | disjIntro1 ψf d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨hc, hO⟩ := hchk
          subst hc; subst hO
          have H := ih Γ c o hd hG ρ hΓ
          exact Or.inl H
  | disjIntro2 φf d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨hc, hO⟩ := hchk
          subst hc; subst hO
          have H := ih Γ c o hd hG ρ hΓ
          exact Or.inr H
  | disjElim d dL dR ih ihL ihR =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | disj a b =>
              simp only [hd] at hchk
              cases hdL : check (a :: Γ) dL with
              | none => simp [hdL] at hchk
              | some cpL =>
                  obtain ⟨χ1, o₁⟩ := cpL
                  cases hdR : check (b :: Γ) dR with
                  | none => simp [hdL, hdR] at hchk
                  | some cpR =>
                      obtain ⟨χ2, o₂⟩ := cpR
                      simp only [hdL, hdR] at hchk
                      split at hchk
                      · rename_i hchi
                        simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                        obtain ⟨hc, hO⟩ := hchk
                        subst hc; subst hO
                        have Hd := ih Γ (DFormula.disj a b) o hd
                          (Gated.union_left (Gated.union_left hG)) ρ hΓ
                        simp only [DFormula.sat] at Hd
                        rcases Hd with ha | hb
                        · exact ihL (a :: Γ) χ1 o₁ hdL
                            (Gated.union_right (Gated.union_left hG)) ρ (CtxSat.cons ha hΓ)
                        · have HR := ihR (b :: Γ) χ2 o₂ hdR
                            (Gated.union_right hG) ρ (CtxSat.cons hb hΓ)
                          rw [hchi]
                          exact HR
                      · nomatch hchk
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | flsElim φf d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | fls =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨hc, hO⟩ := hchk
              subst hc; subst hO
              have H := ih Γ DFormula.fls o hd hG ρ hΓ
              exact H.elim
          | eq _ _ => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | allIntro d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check (Γ.map (DFormula.lift 1 0)) d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨hc, hO⟩ := hchk
          subst hc; subst hO
          simp only [DFormula.sat]
          intro n
          exact ih (Γ.map (DFormula.lift 1 0)) c o hd hG (Env.cons n ρ) (CtxSat.mapLift n hΓ)
  | allElim t d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | all a =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨hc, hO⟩ := hchk
              subst hc; subst hO
              have H := ih Γ (DFormula.all a) o hd hG ρ hΓ
              rw [DFormula.sat_subst0]
              exact H (t.eval ρ)
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | exIntro φf t d ih =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd] at hchk
          split at hchk
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hchk
            obtain ⟨hc, hO⟩ := hchk
            subst hc; subst hO
            have H := ih Γ c o hd hG ρ hΓ
            simp only [DFormula.sat]
            refine ⟨t.eval ρ, ?_⟩
            rw [hcond] at H
            rw [DFormula.sat_subst0] at H
            exact H
          · nomatch hchk
  | exElim ψf d dBody ih ihBody =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | ex a =>
              simp only [hd] at hchk
              cases hdB : check (a :: Γ.map (DFormula.lift 1 0)) dBody with
              | none => simp [hdB] at hchk
              | some cpB =>
                  obtain ⟨χ, o₂⟩ := cpB
                  simp only [hdB] at hchk
                  split at hchk
                  · rename_i hcond
                    simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                    obtain ⟨hc, hO⟩ := hchk
                    subst hc; subst hO
                    have Hex := ih Γ (DFormula.ex a) o hd (Gated.union_left hG) ρ hΓ
                    simp only [DFormula.sat] at Hex
                    obtain ⟨n, hn⟩ := Hex
                    have hctx : CtxSat (Env.cons n ρ) (a :: (Γ.map (DFormula.lift 1 0))) :=
                      CtxSat.cons hn (CtxSat.mapLift n hΓ)
                    have HB := ihBody (a :: Γ.map (DFormula.lift 1 0)) χ o₂ hdB
                      (Gated.union_right hG) (Env.cons n ρ) hctx
                    rw [hcond] at HB
                    rw [DFormula.sat_lift0] at HB
                    exact HB
                  · nomatch hchk
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
  | emPosit φf =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, hO⟩ := hchk
      subst hc; subst hO
      have hem : MetaEM := hG.1 rfl
      simp only [DFormula.sat, DFormula.neg]
      exact hem (DFormula.sat ρ φf)
  | lpoPosit φf =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      obtain ⟨hc, hO⟩ := hchk
      subst hc; subst hO
      have hlpo : MetaLPO := hG.2.1 rfl
      simp only [DFormula.sat, DFormula.neg]
      intro hdec
      exact hlpo (fun n => DFormula.sat (Env.cons n ρ) φf) hdec
  | mpPosit φf =>
      intro Γ φ O hchk hG ρ hΓ
      simp only [check] at hchk
      split at hchk
      · rename_i hqf
        simp only [Option.some.injEq, Prod.mk.injEq] at hchk
        obtain ⟨hc, hO⟩ := hchk
        subst hc; subst hO
        have hmp : MetaMP := hG.2.2 rfl
        have hdec : ∀ n, DFormula.sat (Env.cons n ρ) φf ∨ ¬ DFormula.sat (Env.cons n ρ) φf :=
          fun n => satQF_dec φf hqf (Env.cons n ρ)
        simp only [DFormula.sat, DFormula.neg]
        intro hnn
        exact hmp (fun n => DFormula.sat (Env.cons n ρ) φf) hdec hnn
      · nomatch hchk

/-! ## The two corollaries: FORCED (choice-free) and CLASSICAL -/

/-- FORCED soundness: a derivation the kernel accepts with the EMPTY ledger is
true in the canonical model, with NONE of the three metatheoretic principles.
The gates are discharged vacuously (`Gated.empty`), so the proof term never
touches EM/LPO/MP or `Classical.choice`. `#print axioms sound_forced` is the
kernel's own σ0 / DELTA_FORCED self-audit. -/
theorem sound_forced {d : Deriv} {φ : DFormula} (h : Forced [] d φ) :
    ∀ ρ : Env, DFormula.sat ρ φ := by
  intro ρ
  refine sound_cond d [] φ Ledger.empty h Gated.empty ρ ?_
  intro ψ hψ
  cases hψ

/-- CLASSICAL soundness: ANY accepted derivation is true, supplying the three
principles from the ambient classical metatheory. This is the "run the kernel
over classical metatheory" reading, and it is the ONE place `Classical.choice`
legitimately enters, recorded, by design, exactly as the ledger would demand of
a maximally posit-heavy derivation. -/
theorem sound_classical {Γ : Ctx} {d : Deriv} {φ : DFormula} {O : Ledger}
    (h : check Γ d = some (φ, O)) (ρ : Env) (hΓ : CtxSat ρ Γ) :
    DFormula.sat ρ φ := by
  refine sound_cond d Γ φ O h ?_ ρ hΓ
  refine ⟨fun _ P => Classical.em P, fun _ P _ => ?_, fun _ P _ hnn => ?_⟩
  · exact (Classical.em (∃ n, P n)).elim Or.inl
      (fun hne => Or.inr (fun n hn => hne ⟨n, hn⟩))
  · exact Classical.byContradiction (fun hne => hnn hne)

/-! σ0 self-audit. Expected for `sound_forced`: base logical axioms only (no
`Classical.choice`). This IS the kernel's forcing-spectrum verdict applied to
its own soundness: the FORCED fragment is certified without omniscience. -/
#print axioms sound_forced

#print axioms sound_cond

#print axioms sound_classical

end DeltaKernel
end IndisputableMonolith
