import IndisputableMonolith.Gravity.SevenGaps.Gap2JEhrhartSpan

/-! # Gap2JDiamondScratch

Scratchpad used while debugging kernel reduction for `Fin` numeral goals during
the C15 J-diamond lattice work. No load-bearing theorems live here; the four small
kernel witnesses below are kept as compiling exhibits and nothing imports them. The
lesson is banked as `L-qg-fin-literal-show-first` in QG memory.

Findings, kept as compiling witnesses:

* `decide` and the `OfNat` simprocs do not unfold non-literal `Fin` bounds
  (projections such as `K.nV`, `K.nE`). Writing `({2} : Finset (Fin
  twoEdgeComplex.nV))` fails `OfNat` synthesis outright, and `fin_cases` over
  `Fin K.nE` leaves residuals `⟨2, ⋯⟩ = 2` that `simp` and `try decide` cannot
  close (they became silent `sorryAx` in the main module before the fix).
* The fix: `show` the definitionally-equal literal form first, then
  `ext` + `fin_cases` + `simp` closes every case. -/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2JDiamondScratch

open PathSumMeasure GaugeHistoryMeasure Gap2PostingCostDerivation Gap2JEhrhartSpan

variable {B : ℕ}

structure SC4 (K : BoundedComplex B) where
  verts : Finset (Fin K.nV)
  edges : Finset (Fin K.nE)

def teLeft : SC4 twoEdgeComplex where
  verts := ({0, 1} : Finset (Fin 4))
  edges := ({0} : Finset (Fin 2))

def teRight : SC4 twoEdgeComplex where
  verts := ({2, 3} : Finset (Fin 4))
  edges := ({1} : Finset (Fin 2))

-- projections with a non-literal bound: this one simp can still close
theorem teInterEmpty : teLeft.verts ∩ teRight.verts = ∅ := by
  ext v
  fin_cases v <;> simp [teLeft, teRight]

-- the working pattern for the case simp cannot: `show` the literal form first
theorem teInter2 : teLeft.verts ∩ teRight.verts =
    (({0, 1} : Finset (Fin 4)) ∩ ({2, 3} : Finset (Fin 4))) := rfl

theorem inter4literal : (({0, 1, 2} : Finset (Fin 4)) ∩ ({2, 3} : Finset (Fin 4))) = {2} := by
  ext v
  fin_cases v <;> simp

-- a Fin 4 numeral equality `decide` closes when the bound is literal
theorem fin4decide : (⟨2, by decide⟩ : Fin 4) = 2 := by decide

end Gap2JDiamondScratch
end SevenGaps
end Gravity
end IndisputableMonolith
