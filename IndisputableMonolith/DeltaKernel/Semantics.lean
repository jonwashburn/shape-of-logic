import IndisputableMonolith.DeltaKernel.Syntax

/-!
# δ-Kernel: Semantics in the Canonical Model

The canonical model of the distinction signature is the free distinction
structure itself, whose host image is `Nat` (the paper's ℕδ ≅ ℕ, forced by
initiality). Terms evaluate to `Nat`; formulas to host `Prop` with the
intuitionistic reading of the connectives. Nothing here uses classical
logic: every lemma in this file is proved constructively, so the FORCED
soundness theorem downstream (`Sound.lean`) can itself be axiom-audited as
choice-free. That audit is the kernel's own σ-ledger applied to the kernel.

Contents:
- `Env`: de Bruijn valuations `Nat → Nat`, with `cons` for binder entry.
- `DTerm.eval`, `DFormula.sat`: the interpretation.
- The de Bruijn commutation lemmas (`eval_lift`, `eval_subst`, `sat_lift`,
  `sat_subst`) and their binder-instance corollaries (`sat_lift0`,
  `sat_subst0`, `sat_stepSucc`) — exactly the facts the soundness proof
  needs for ∀-intro/elim, ∃-intro/elim, Leibniz substitution, and the
  induction rule.

No Mathlib. Imports only the kernel's own syntax.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- Environments: de Bruijn valuations into the canonical model ℕ. -/
def Env : Type := Nat → Nat

namespace Env

/-- Extend an environment under a binder: variable 0 gets `v`, everything
else shifts up. -/
def cons (v : Nat) (ρ : Env) : Env := fun n =>
  match n with
  | 0 => v
  | n + 1 => ρ n

@[simp] theorem cons_zero (v : Nat) (ρ : Env) : cons v ρ 0 = v := rfl

@[simp] theorem cons_succ (v : Nat) (ρ : Env) (n : Nat) :
    cons v ρ (n + 1) = ρ n := rfl

/-- The environment transform matching `subst k s`: variable `k` reads the
substituted value, variables above `k` shift down. -/
def substAt (k v : Nat) (ρ : Env) : Env := fun n =>
  if n = k then v else if k < n then ρ (n - 1) else ρ n

/-- `substAt 0` is `cons`, pointwise. -/
theorem substAt_zero (v : Nat) (ρ : Env) :
    ∀ n, substAt 0 v ρ n = cons v ρ n := by
  intro n
  cases n with
  | zero => simp [substAt]
  | succ m => simp [substAt]

/-- `substAt` commutes with `cons` at a shifted index, pointwise. This is
the binder case of the substitution lemma. -/
theorem substAt_cons (k v w : Nat) (ρ : Env) :
    ∀ n, substAt (k + 1) v (cons w ρ) n = cons w (substAt k v ρ) n := by
  intro n
  cases n with
  | zero =>
      show (if 0 = k + 1 then v
            else if k + 1 < 0 then cons w ρ (0 - 1) else cons w ρ 0) = w
      have h1 : ¬ (0 = k + 1) := by omega
      have h2 : ¬ (k + 1 < 0) := by omega
      rw [if_neg h1, if_neg h2]
      rfl
  | succ m =>
      show (if m + 1 = k + 1 then v
            else if k + 1 < m + 1 then cons w ρ (m + 1 - 1) else cons w ρ (m + 1))
          = (if m = k then v else if k < m then ρ (m - 1) else ρ m)
      cases Nat.decEq m k with
      | isTrue h =>
          have h1 : m + 1 = k + 1 := by omega
          rw [if_pos h1, if_pos h]
      | isFalse h =>
          have h1 : ¬ (m + 1 = k + 1) := by omega
          rw [if_neg h1, if_neg h]
          cases Nat.decLt k m with
          | isTrue h2 =>
              have h3 : k + 1 < m + 1 := by omega
              rw [if_pos h3, if_pos h2]
              obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
              rfl
          | isFalse h2 =>
              have h3 : ¬ (k + 1 < m + 1) := by omega
              rw [if_neg h3, if_neg h2]
              rfl

end Env

/-- The variable renaming performed by `lift d c`. -/
def liftVar (d c n : Nat) : Nat := if n < c then n else n + d

@[simp] theorem liftVar_one_zero (n : Nat) : liftVar 1 0 n = n + 1 := by
  simp [liftVar]

/-- `liftVar` at a raised cutoff commutes with `cons`, pointwise. This is
the binder case of the lifting lemma. -/
theorem cons_liftVar (v d c : Nat) (ρ : Env) :
    ∀ n, Env.cons v ρ (liftVar d (c + 1) n) =
      Env.cons v (fun m => ρ (liftVar d c m)) n := by
  intro n
  cases n with
  | zero => simp [liftVar]
  | succ m =>
    by_cases h : m < c
    · have h' : m + 1 < c + 1 := by omega
      simp [liftVar, h, h']
    · have h' : ¬ (m + 1 < c + 1) := by omega
      have e : m + 1 + d = (m + d) + 1 := by omega
      simp [liftVar, h, h', e]

namespace DTerm

/-- Evaluation of terms in the canonical model. -/
def eval (ρ : Env) : DTerm → Nat
  | var n => ρ n
  | zero => 0
  | succ t => eval ρ t + 1
  | add t s => eval ρ t + eval ρ s
  | mul t s => eval ρ t * eval ρ s

/-- Evaluation respects pointwise-equal environments (no funext needed). -/
theorem eval_ext {ρ ρ' : Env} (h : ∀ n, ρ n = ρ' n) :
    ∀ t : DTerm, eval ρ t = eval ρ' t
  | var n => h n
  | zero => rfl
  | succ t => by simp [eval, eval_ext h t]
  | add t s => by simp [eval, eval_ext h t, eval_ext h s]
  | mul t s => by simp [eval, eval_ext h t, eval_ext h s]

/-- Lifting commutes with evaluation through the variable renaming. -/
theorem eval_lift (d c : Nat) (ρ : Env) : ∀ t : DTerm,
    eval ρ (t.lift d c) = eval (fun n => ρ (liftVar d c n)) t
  | var n => by
      by_cases h : n < c <;> simp [lift, eval, liftVar, h]
  | zero => rfl
  | succ t => by simp [lift, eval, eval_lift d c ρ t]
  | add t s => by simp [lift, eval, eval_lift d c ρ t, eval_lift d c ρ s]
  | mul t s => by simp [lift, eval, eval_lift d c ρ t, eval_lift d c ρ s]

/-- Substitution commutes with evaluation through `substAt`. -/
theorem eval_subst (k : Nat) (s : DTerm) (ρ : Env) : ∀ t : DTerm,
    eval ρ (DTerm.subst k s t) = eval (Env.substAt k (s.eval ρ) ρ) t
  | var n => by
      by_cases h1 : n = k
      · simp [subst, eval, Env.substAt, h1]
      · by_cases h2 : k < n
        · simp [subst, eval, Env.substAt, h1, h2]
        · simp [subst, eval, Env.substAt, h1, h2]
  | zero => rfl
  | succ t => by simp [subst, eval, eval_subst k s ρ t]
  | add t u => by simp [subst, eval, eval_subst k s ρ t, eval_subst k s ρ u]
  | mul t u => by simp [subst, eval, eval_subst k s ρ t, eval_subst k s ρ u]

/-- Numerals evaluate to the metatheoretic naturals they name. -/
@[simp] theorem eval_ofNat (ρ : Env) : ∀ n : Nat, eval ρ (ofNat n) = n
  | 0 => rfl
  | n + 1 => by simp [ofNat, eval, eval_ofNat ρ n]

end DTerm

namespace DFormula

/-- Satisfaction in the canonical model, with the intuitionistic reading of
the connectives (the host `Prop` connectives, used constructively). -/
def sat (ρ : Env) : DFormula → Prop
  | eq t s => t.eval ρ = s.eval ρ
  | fls => False
  | conj a b => sat ρ a ∧ sat ρ b
  | disj a b => sat ρ a ∨ sat ρ b
  | impl a b => sat ρ a → sat ρ b
  | all a => ∀ n : Nat, sat (Env.cons n ρ) a
  | ex a => ∃ n : Nat, sat (Env.cons n ρ) a

/-- Satisfaction respects pointwise-equal environments. -/
theorem sat_ext : ∀ (φ : DFormula) {ρ ρ' : Env},
    (∀ n, ρ n = ρ' n) → (sat ρ φ ↔ sat ρ' φ)
  | eq t s, ρ, ρ', h => by
      simp [sat, DTerm.eval_ext h t, DTerm.eval_ext h s]
  | fls, _, _, _ => Iff.rfl
  | conj a b, ρ, ρ', h => by
      simp [sat]
      exact and_congr (sat_ext a h) (sat_ext b h)
  | disj a b, ρ, ρ', h => by
      simp [sat]
      exact or_congr (sat_ext a h) (sat_ext b h)
  | impl a b, ρ, ρ', h => by
      simp only [sat]
      exact imp_congr (sat_ext a h) (sat_ext b h)
  | all a, ρ, ρ', h => by
      simp only [sat]
      constructor
      · intro hall n
        exact (sat_ext a (fun m => by cases m <;> simp [h _])).mp (hall n)
      · intro hall n
        exact (sat_ext a (fun m => by cases m <;> simp [h _])).mpr (hall n)
  | ex a, ρ, ρ', h => by
      simp only [sat]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, (sat_ext a (fun m => by cases m <;> simp [h _])).mp hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, (sat_ext a (fun m => by cases m <;> simp [h _])).mpr hn⟩

/-- Lifting commutes with satisfaction through the variable renaming. -/
theorem sat_lift (d : Nat) (φ : DFormula) : ∀ (c : Nat) (ρ : Env),
    sat ρ (φ.lift d c) ↔ sat (fun n => ρ (liftVar d c n)) φ := by
  induction φ with
  | eq t s =>
      intro c ρ
      simp [lift, sat, DTerm.eval_lift]
  | fls => intro c ρ; exact Iff.rfl
  | conj a b iha ihb =>
      intro c ρ
      simp only [lift, sat]
      exact and_congr (iha c ρ) (ihb c ρ)
  | disj a b iha ihb =>
      intro c ρ
      simp only [lift, sat]
      exact or_congr (iha c ρ) (ihb c ρ)
  | impl a b iha ihb =>
      intro c ρ
      simp only [lift, sat]
      exact imp_congr (iha c ρ) (ihb c ρ)
  | all a ih =>
      intro c ρ
      simp only [lift, sat]
      constructor
      · intro h n
        exact (sat_ext a (cons_liftVar n d c ρ)).mp ((ih (c + 1) (Env.cons n ρ)).mp (h n))
      · intro h n
        exact (ih (c + 1) (Env.cons n ρ)).mpr ((sat_ext a (cons_liftVar n d c ρ)).mpr (h n))
  | ex a ih =>
      intro c ρ
      simp only [lift, sat]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, (sat_ext a (cons_liftVar n d c ρ)).mp ((ih (c + 1) (Env.cons n ρ)).mp hn)⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, (ih (c + 1) (Env.cons n ρ)).mpr ((sat_ext a (cons_liftVar n d c ρ)).mpr hn)⟩

/-- Substitution commutes with satisfaction through `substAt`. -/
theorem sat_subst (φ : DFormula) : ∀ (k : Nat) (s : DTerm) (ρ : Env),
    sat ρ (φ.subst k s) ↔ sat (Env.substAt k (s.eval ρ) ρ) φ := by
  induction φ with
  | eq t u =>
      intro k s ρ
      simp [subst, sat, DTerm.eval_subst]
  | fls => intro k s ρ; exact Iff.rfl
  | conj a b iha ihb =>
      intro k s ρ
      simp only [subst, sat]
      exact and_congr (iha k s ρ) (ihb k s ρ)
  | disj a b iha ihb =>
      intro k s ρ
      simp only [subst, sat]
      exact or_congr (iha k s ρ) (ihb k s ρ)
  | impl a b iha ihb =>
      intro k s ρ
      simp only [subst, sat]
      exact imp_congr (iha k s ρ) (ihb k s ρ)
  | all a ih =>
      intro k s ρ
      simp only [subst, sat]
      have key : ∀ n : Nat,
          sat (Env.cons n ρ) (a.subst (k + 1) (s.lift 1 0)) ↔
          sat (Env.cons n (Env.substAt k (s.eval ρ) ρ)) a := by
        intro n
        have e1 : (s.lift 1 0).eval (Env.cons n ρ) = s.eval ρ := by
          rw [DTerm.eval_lift]
          exact DTerm.eval_ext (fun m => by simp) s
        rw [ih (k + 1) (s.lift 1 0) (Env.cons n ρ), e1]
        exact sat_ext a (Env.substAt_cons k (s.eval ρ) n ρ)
      constructor
      · intro h n; exact (key n).mp (h n)
      · intro h n; exact (key n).mpr (h n)
  | ex a ih =>
      intro k s ρ
      simp only [subst, sat]
      have key : ∀ n : Nat,
          sat (Env.cons n ρ) (a.subst (k + 1) (s.lift 1 0)) ↔
          sat (Env.cons n (Env.substAt k (s.eval ρ) ρ)) a := by
        intro n
        have e1 : (s.lift 1 0).eval (Env.cons n ρ) = s.eval ρ := by
          rw [DTerm.eval_lift]
          exact DTerm.eval_ext (fun m => by simp) s
        rw [ih (k + 1) (s.lift 1 0) (Env.cons n ρ), e1]
        exact sat_ext a (Env.substAt_cons k (s.eval ρ) n ρ)
      constructor
      · rintro ⟨n, hn⟩; exact ⟨n, (key n).mp hn⟩
      · rintro ⟨n, hn⟩; exact ⟨n, (key n).mpr hn⟩

/-- Binder-entry instance of the lifting lemma: a formula lifted over one
fresh variable ignores that variable. Used for ∀-intro, ∃-elim, and
context weakening under binders. -/
theorem sat_lift0 (φ : DFormula) (v : Nat) (ρ : Env) :
    sat (Env.cons v ρ) (φ.lift 1 0) ↔ sat ρ φ := by
  rw [sat_lift]
  exact sat_ext φ (fun n => by simp)

/-- Binder-instantiation instance of the substitution lemma. Used for
∀-elim, ∃-intro, Leibniz substitution, and the induction base. -/
theorem sat_subst0 (φ : DFormula) (t : DTerm) (ρ : Env) :
    sat ρ (φ.subst 0 t) ↔ sat (Env.cons (t.eval ρ) ρ) φ := by
  rw [sat_subst]
  exact sat_ext φ (Env.substAt_zero (t.eval ρ) ρ)

/-- The induction-step body means exactly "φ one distinction step up". -/
theorem sat_stepSucc (φ : DFormula) (n : Nat) (ρ : Env) :
    sat (Env.cons n ρ) φ.stepSucc ↔ sat (Env.cons (n + 1) ρ) φ := by
  unfold stepSucc
  rw [sat_subst0]
  have e : (DTerm.succ (DTerm.var 0)).eval (Env.cons n ρ) = n + 1 := rfl
  rw [e, sat_lift]
  refine sat_ext φ (fun m => ?_)
  cases m with
  | zero => simp [liftVar]
  | succ j =>
      have h' : ¬ (j + 1 < 1) := by omega
      have e2 : j + 1 + 1 = (j + 1) + 1 := rfl
      simp [liftVar, h']

end DFormula

end DeltaKernel
end IndisputableMonolith
