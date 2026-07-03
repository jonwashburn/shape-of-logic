import Mathlib
import IndisputableMonolith.Recognition
import IndisputableMonolith.Causality.Basic

namespace IndisputableMonolith
namespace Potential

/-! Dependency-light T4 uniqueness lemmas on discrete reach sets. -/

variable {M : Recognition.RecognitionStructure}

abbrev Pot (M : Recognition.RecognitionStructure) := M.U → ℤ

/-- Discrete edge rule: along any edge, `p` increases by `δ` on `M.R`. -/
def DE (δ : ℤ) (p : Pot M) : Prop := ∀ {a b}, M.R a b → p b - p a = δ

/-- Package the recognition relation as a kinematics. -/
def Kin (M : Recognition.RecognitionStructure) : Causality.Kinematics M.U := { step := M.R }

/-- On each edge, the difference (p − q) is invariant if both satisfy the same δ rule. -/
lemma edge_diff_invariant {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {a b : M.U} (h : M.R a b) :
  (p b - q b) = (p a - q a) := by
  have harr : (p b - q b) - (p a - q a) = (p b - p a) - (q b - q a) := by ring
  have hδ : (p b - p a) - (q b - q a) = δ - δ := by simp [hp h, hq h]
  have : (p b - q b) - (p a - q a) = 0 := by simp [harr, hδ]
  exact sub_eq_zero.mp this

/-- The difference (p − q) is constant along any n‑step reach. -/
lemma diff_const_on_ReachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → (p y - q y) = (p x - q x) := by
  intro n x y h
  induction h with
  | zero => rfl
  | @succ n x y z hxy hyz ih =>
      have h_edge : (p z - q z) = (p y - q y) :=
        edge_diff_invariant (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq hyz
      exact h_edge.trans ih

/-- On reach components, the difference (p − q) equals its basepoint value. -/
lemma diff_const_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hreach : Causality.Reaches (Kin M) x0 y) :
  (p y - q y) = (p x0 - q x0) := by
  rcases hreach with ⟨n, h⟩
  simpa using diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (n:=n) (x:=x0) (y:=y) h

/-- If two δ‑potentials agree at a basepoint, they agree on its n-step reach set. -/
theorem T4_unique_on_reachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 : M.U}
  (hbase : p x0 = q x0) : ∀ {n y}, Causality.ReachN (Kin M) n x0 y → p y = q y := by
  intro n y h
  have hdiff := diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq h
  have : p x0 - q x0 = 0 := by simp [hbase]
  have : p y - q y = 0 := by simpa [this] using hdiff
  exact sub_eq_zero.mp this

/-- Componentwise uniqueness: if p and q agree at x0, then they agree at every y reachable from x0. -/
theorem T4_unique_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0)
  (hreach : Causality.Reaches (Kin M) x0 y) : p y = q y := by
  rcases hreach with ⟨n, h⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=n) (y:=y) h

/-- If y lies in the n-ball around x0, then the two δ-potentials agree at y. -/
theorem T4_unique_on_inBall {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0) {n : Nat}
  (hin : Causality.inBall (Kin M) x0 n y) : p y = q y := by
  rcases hin with ⟨k, _, hreach⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=k) (y:=y) hreach

/-- Componentwise uniqueness up to a constant: there exists `c` (the basepoint offset)
    such that on the reach component of `x0` we have `p y = q y + c` for all `y`. -/
theorem T4_unique_up_to_const_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 : M.U} :
  ∃ c : ℤ, ∀ {y : M.U}, Causality.Reaches (Kin M) x0 y → p y = q y + c := by
  refine ⟨p x0 - q x0, ?_⟩
  intro y hreach
  have hdiff := diff_const_on_component (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) (y:=y) hreach
  -- rearrange `p y - q y = c` to `p y = q y + c`
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
    (eq_add_of_sub_eq hdiff)

/-- T8 quantization lemma: along any n-step reach, `p` changes by exactly `n·δ`. -/
lemma increment_on_ReachN {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → p y - p x = (n : ℤ) * δ := by
  intro n x y h
  induction h with
  | zero =>
      simp
  | @succ n x y z hxy hyz ih =>
      -- p z - p x = (p z - p y) + (p y - p x) = δ + n·δ = (n+1)·δ
      have hz : p z - p y = δ := hp hyz
      calc
        p z - p x = (p z - p y) + (p y - p x) := by ring
        _ = δ + (n : ℤ) * δ := by simpa [hz, ih]
        _ = ((n : ℤ) + 1) * δ := by ring
        _ = ((Nat.succ n : Nat) : ℤ) * δ := by
              simp [Nat.cast_add]

/-- Corollary: the set of potential differences along reaches is the δ-generated subgroup. -/
lemma diff_in_deltaSub {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) {n x y}
  (h : Causality.ReachN (Kin M) n x y) : ∃ k : ℤ, p y - p x = k * δ := by
  refine ⟨(n : ℤ), ?_⟩
  simpa using increment_on_ReachN (M:=M) (δ:=δ) (p:=p) hp (n:=n) (x:=x) (y:=y) h

end Potential
end IndisputableMonolith
