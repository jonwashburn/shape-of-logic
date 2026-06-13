import Mathlib
-- LightCone is not required by the minimal Recognition core; avoid heavy deps

namespace IndisputableMonolith
namespace Recognition

/-! ### T1 (MP): Nothing cannot recognize itself -/

abbrev Nothing := Empty

/-- Minimal recognizer→recognized pairing. -/
structure Recognize (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

/-- MP: It is impossible for Nothing to recognize itself. -/
def MP : Prop := ¬ ∃ _ : Recognize Nothing Nothing, True

theorem mp_holds : MP := by
  intro h
  rcases h with ⟨⟨r, _⟩, _⟩
  cases r

/-- Alias used in the manuscript: "Nonexistence cannot recognize itself." -/
abbrev NothingCannotRecognizeItself : Prop := MP

/-- Direct alias proof of MP for the manuscript phrasing. -/
theorem nothing_cannot_recognize_itself : NothingCannotRecognizeItself :=
  mp_holds

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)
def head : M.U := by
  have hpos : 0 < ch.n + 1 := Nat.succ_pos _
  exact ch.f ⟨0, hpos⟩
def last : M.U := by
  have hlt : ch.n < ch.n + 1 := Nat.lt_succ_self _
  exact ch.f ⟨ch.n, hlt⟩
end Chain

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

@[simp] def Ledger.Carrier {M : RecognitionStructure} (_ : Ledger M) : Type :=
  M.U

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

lemma chainFlux_zero_of_loop {M} (L : Ledger M) [Conserves L] (ch : Chain M) (h : ch.head = ch.last) :
  chainFlux L ch = 0 := Conserves.conserve (L:=L) ch h

lemma phi_zero_of_balanced {M} (L : Ledger M) (hbal : ∀ u, L.debit u = L.credit u) :
  ∀ u, phi L u = 0 := by
  intro u; simp [phi, hbal u, sub_self]

lemma chainFlux_zero_of_balanced {M} (L : Ledger M) (ch : Chain M)
  (hbal : ∀ u, L.debit u = L.credit u) :
  chainFlux L ch = 0 := by
  simp [chainFlux, phi_zero_of_balanced (M:=M) L hbal]

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  have huw : u = w := huniq u hu
  have hvw : v = w := huniq v hv
  exact huw.trans hvw.symm

end Recognition

namespace Demo

open Recognition

structure U where
  a : Unit

/-- Recognition relation by structural equality -/
def recog : U → U → Prop := fun x y => x = y

def M : RecognitionStructure := { U := U, R := recog }

def L : Ledger M := { debit := fun _ => 1, credit := fun _ => 1 }

def twoStep : Chain M :=
  { n := 1
  , f := fun _ => ⟨()⟩
  , ok := by intro i; trivial }

example : chainFlux L twoStep = 0 := by
  have hbal : ∀ u, L.debit u = L.credit u := by intro _; rfl
  simpa [chainFlux_zero_of_balanced (M:=M) L twoStep hbal]

end Demo

-- Moved advanced Recognition sections (ClassicalBridge, Potential uniqueness) to Recognition/WIP.lean during modularization.
