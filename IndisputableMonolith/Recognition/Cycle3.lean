import Mathlib
import IndisputableMonolith.Recognition

namespace IndisputableMonolith
namespace Cycle3

open Recognition

def M : RecognitionStructure :=
  { U := Fin 3
  , R := fun i j => j = ⟨(i.val + 1) % 3, by
      have h : (i.val + 1) % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
      simpa using h⟩ }

def L : Ledger M :=
  { debit := fun _ => 0
  , credit := fun _ => 0 }

instance : Conserves L :=
  { conserve := by
      intro ch hclosed
      -- phi is identically 0, so flux is 0
      simp [chainFlux, phi, hclosed] }

def postedAt : Nat → M.U → Prop := fun t v =>
  v = ⟨t % 3, by
    have : t % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
    simpa using this⟩

instance : AtomicTick M :=
  { postedAt := postedAt
  , unique_post := by
      intro t
      refine ⟨⟨t % 3, ?_⟩, ?_, ?_⟩
      · have : t % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
        simpa using this
      · rfl
      · intro u hu
        simpa [postedAt] using hu }

end Cycle3
end IndisputableMonolith
