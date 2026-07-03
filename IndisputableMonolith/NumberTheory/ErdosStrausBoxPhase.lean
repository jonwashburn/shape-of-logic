import Mathlib
import IndisputableMonolith.NumberTheory.ErdosStrausRotationHierarchy

/-!
# Erdős-Straus Square-Budget Box Phase

This module isolates the finite combinatorial part of the residual
Erdős-Straus proof.

For a square budget `N^2`, a divisor exponent box is represented by a
complementary pair `(d,e)` with `d*e = N^2`.  This is equivalent to choosing
exponents `0 ≤ a_p ≤ 2 v_p(N)` in the prime factorization, but it avoids
unnecessary factorization API overhead in the finite closure lemma.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ErdosStrausBoxPhase

open ErdosStrausRotationHierarchy

/-- A divisor exponent-box point for the square budget `N^2`, represented
by a divisor `d` and its complementary divisor `e`. -/
structure DivisorExponentBox (N : ℕ) where
  d : ℕ
  e : ℕ
  d_pos : 0 < d
  e_pos : 0 < e
  square_budget : d * e = N ^ 2

/-- The divisor selected by a box point. -/
def boxDivisor {N : ℕ} (box : DivisorExponentBox N) : ℕ :=
  box.d

/-- The complementary divisor selected by a box point. -/
def boxComplement {N : ℕ} (box : DivisorExponentBox N) : ℕ :=
  box.e

theorem box_divisor_mul_complement {N : ℕ} (box : DivisorExponentBox N) :
    boxDivisor box * boxComplement box = N ^ 2 :=
  box.square_budget

/-- A square-budget box hits the balanced residual phase for gate `c`.

The conditions `c | N+d` and `c | N+e` say exactly that both reciprocal
defects land in phase `-N` modulo `c`. -/
def HitsBalancedPhase (n c : ℕ) : Prop :=
  ∃ x N : ℕ, ∃ box : DivisorExponentBox N,
    0 < n ∧ 0 < c ∧ 0 < x ∧ 0 < N ∧
    N = n * x ∧
    c = 4 * x - n ∧
    c ∣ N + boxDivisor box ∧
    c ∣ N + boxComplement box

/-- The finite box-to-pair closure lemma.  A box phase hit is exactly the
balanced-pair support required by the RCL skeleton. -/
theorem box_phase_hit_gives_balanced_pair {n c : ℕ}
    (h : HitsBalancedPhase n c) :
    BalancedPairPhaseSupport n c := by
  rcases h with ⟨x, N, box, hn, hc, hx, hNpos, hN, hcdef, hdvd, hevd⟩
  refine ⟨x, N, boxDivisor box, boxComplement box,
    hn, hc, hx, hNpos, box.d_pos, box.e_pos, hN, hcdef, ?_, hdvd, hevd⟩
  exact box_divisor_mul_complement box

/-- A box phase hit already gives a rational Erdős-Straus representation,
by composing the finite closure lemma with the RCL ledger theorem. -/
theorem box_phase_hit_gives_repr {n c : ℕ}
    (h : HitsBalancedPhase n c) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  balanced_pair_phase_support_gives_repr (box_phase_hit_gives_balanced_pair h)

end ErdosStrausBoxPhase
end NumberTheory
end IndisputableMonolith
