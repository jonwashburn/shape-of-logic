import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Potential
import IndisputableMonolith.Causality.Basic
-- For standalone WIP, inline a minimal Kinematics to avoid module dependency
namespace Local
structure Kinematics (α : Type) where
  step : α → α → Prop
inductive ReachN {α} (K : Kinematics α) : Nat → α → α → Prop
| zero {x} : ReachN K 0 x x
| succ {n x y z} : ReachN K n x y → K.step y z → ReachN K (n+1) x z
def inBall {α} (K : Kinematics α) (x : α) (n : Nat) (y : α) : Prop := ∃ k ≤ n, ReachN K k x y
def Reaches {α} (K : Kinematics α) (x y : α) : Prop := ∃ n, ReachN K n x y
end Local

namespace IndisputableMonolith
namespace LedgerUniqueness

open Recognition

variable {M : Recognition.RecognitionStructure}

def IsAffine (δ : ℤ) (L : Recognition.Ledger M) : Prop :=
  Potential.DE (M:=M) δ (fun x => Recognition.phi L x)

lemma unique_on_reachN {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} (hbase : Recognition.phi L x0 = Recognition.phi L' x0) :
  ∀ {n y}, Causality.ReachN (Potential.Kin M) n x0 y →
    Recognition.phi L y = Recognition.phi L' y := by
  intro n y hreach
  have : (fun x => Recognition.phi L x) y = (fun x => Recognition.phi L' x) y := by
    refine Potential.T4_unique_on_reachN (M:=M) (δ:=δ)
      (p:=fun x => Recognition.phi L x) (q:=fun x => Recognition.phi L' x)
      hL hL' (x0:=x0) (by simpa using hbase) (n:=n) (y:=y) hreach
  simpa using this

lemma unique_on_inBall {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 y : M.U} (hbase : Recognition.phi L x0 = Recognition.phi L' x0) {n : Nat}
  (hin : Causality.inBall (Potential.Kin M) x0 n y) :
  Recognition.phi L y = Recognition.phi L' y := by
  exact Potential.T4_unique_on_inBall (M:=M) (δ:=δ)
    (p:=fun x => Recognition.phi L x) (q:=fun x => Recognition.phi L' x)
    hL hL' (x0:=x0) (by simpa using hbase) (n:=n) hin

lemma unique_up_to_const_on_component {δ : ℤ} {L L' : Recognition.Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} : ∃ c : ℤ, ∀ {y : M.U}, Causality.Reaches (Potential.Kin M) x0 y →
    Recognition.phi L y = Recognition.phi L' y + c := by
  simpa using
    (Potential.T4_unique_up_to_const_on_component (M:=M) (δ:=δ)
      (p:=fun x => Recognition.phi L x) (q:=fun x => Recognition.phi L' x)
      hL hL' (x0:=x0))

end LedgerUniqueness
end IndisputableMonolith


