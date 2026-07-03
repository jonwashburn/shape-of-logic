import Mathlib

namespace IndisputableMonolith

/-- Minimal RecognitionStructure stub for standalone compilation -/
structure RecognitionStructure where
  U : Type
  R : U → U → Prop

/-- Chain structure with minimal axioms for standalone compilation -/
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

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (ch.last) - phi L (ch.head)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

/-- ## T2 (Atomicity): unique posting per tick implies no collision at a tick. -/
theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  have hu' : u = w := huniq u hu
  have hv' : v = w := huniq v hv
  exact hu'.trans hv'.symm

theorem T3_continuity {M} (L : Ledger M) [Conserves L] :
  ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0 := Conserves.conserve

end IndisputableMonolith
