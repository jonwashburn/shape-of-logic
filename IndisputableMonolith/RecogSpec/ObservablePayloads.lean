import Mathlib

/-!
# Observable Payloads (Typed)

Strongly typed records for the dimensionless mass-ratio and mixing-angle
payloads.  These replace the raw `List ℝ` fields that previously encoded
position-dependent semantics.

## Canonical semantics

  LeptonMassRatios : { mu_over_e, tau_over_e, tau_over_mu }
  CkmMixingAngles  : { vus, vcb, vub }
-/

namespace IndisputableMonolith
namespace RecogSpec

/-- Lepton-sector inter-generation mass ratios (dimensionless). -/
structure LeptonMassRatios where
  mu_over_e   : ℝ
  tau_over_e  : ℝ
  tau_over_mu : ℝ

/-- CKM mixing-angle magnitudes (dimensionless). -/
structure CkmMixingAngles where
  vus : ℝ
  vcb : ℝ
  vub : ℝ

namespace LeptonMassRatios

/-- Canonical list view: `[μ/e, τ/e, τ/μ]`. -/
def toList (m : LeptonMassRatios) : List ℝ :=
  [m.mu_over_e, m.tau_over_e, m.tau_over_mu]

@[simp] theorem toList_length (m : LeptonMassRatios) : m.toList.length = 3 := rfl

/-- Every field satisfies a predicate. -/
def Forall (P : ℝ → Prop) (m : LeptonMassRatios) : Prop :=
  P m.mu_over_e ∧ P m.tau_over_e ∧ P m.tau_over_mu

theorem forall_iff_list (P : ℝ → Prop) (m : LeptonMassRatios) :
    m.Forall P ↔ ∀ r ∈ m.toList, P r := by
  simp only [Forall, toList, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨h1, h2, h3⟩ r (rfl | rfl | rfl) <;> assumption
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))⟩

@[ext] theorem ext {a b : LeptonMassRatios}
    (h1 : a.mu_over_e = b.mu_over_e)
    (h2 : a.tau_over_e = b.tau_over_e)
    (h3 : a.tau_over_mu = b.tau_over_mu) : a = b := by
  cases a; cases b; simp_all

theorem toList_injective {a b : LeptonMassRatios} (h : a.toList = b.toList) : a = b := by
  simp only [toList] at h
  have h1 : a.mu_over_e = b.mu_over_e := List.cons.inj h |>.1
  have h23 := List.cons.inj h |>.2
  have h2 : a.tau_over_e = b.tau_over_e := List.cons.inj h23 |>.1
  have h3 : a.tau_over_mu = b.tau_over_mu := List.cons.inj (List.cons.inj h23 |>.2) |>.1
  exact ext h1 h2 h3

@[simp] theorem mk_toList (a b c : ℝ) :
    (⟨a, b, c⟩ : LeptonMassRatios).toList = [a, b, c] := rfl

end LeptonMassRatios

namespace CkmMixingAngles

/-- Canonical list view: `[V_us, V_cb, V_ub]`. -/
def toList (m : CkmMixingAngles) : List ℝ :=
  [m.vus, m.vcb, m.vub]

@[simp] theorem toList_length (m : CkmMixingAngles) : m.toList.length = 3 := rfl

/-- Every field satisfies a predicate. -/
def Forall (P : ℝ → Prop) (m : CkmMixingAngles) : Prop :=
  P m.vus ∧ P m.vcb ∧ P m.vub

theorem forall_iff_list (P : ℝ → Prop) (m : CkmMixingAngles) :
    m.Forall P ↔ ∀ r ∈ m.toList, P r := by
  simp only [Forall, toList, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨h1, h2, h3⟩ r (rfl | rfl | rfl) <;> assumption
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))⟩

@[ext] theorem ext {a b : CkmMixingAngles}
    (h1 : a.vus = b.vus)
    (h2 : a.vcb = b.vcb)
    (h3 : a.vub = b.vub) : a = b := by
  cases a; cases b; simp_all

theorem toList_injective {a b : CkmMixingAngles} (h : a.toList = b.toList) : a = b := by
  simp only [toList] at h
  have h1 : a.vus = b.vus := List.cons.inj h |>.1
  have h23 := List.cons.inj h |>.2
  have h2 : a.vcb = b.vcb := List.cons.inj h23 |>.1
  have h3 : a.vub = b.vub := List.cons.inj (List.cons.inj h23 |>.2) |>.1
  exact ext h1 h2 h3

@[simp] theorem mk_toList (a b c : ℝ) :
    (⟨a, b, c⟩ : CkmMixingAngles).toList = [a, b, c] := rfl

end CkmMixingAngles

end RecogSpec
end IndisputableMonolith
