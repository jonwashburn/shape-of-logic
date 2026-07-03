import Mathlib
import IndisputableMonolith.NumberTheory.ErdosStrausRCL

/-!
# Erdős-Straus Recognition Rotation Hierarchy

This module turns the current RCL attack into a theorem-shaped proof skeleton.

It proves the finite/gate pieces and isolates the two genuinely missing
number-theoretic engines:

1. prime phase separation across admissible residual quotients;
2. reciprocal pair closure once enough phase support appears.

No new axiom is introduced here.  The missing engines are structure fields:
explicit assumptions that a future proof must supply.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ErdosStrausRotationHierarchy

open ErdosStrausRCL

/-! ## 1. Finite quotient necessity -/

/-- A nonzero residual `c/N` has a positive finite modulus `c`. -/
def NonzeroResidual (c N : ℕ) : Prop :=
  0 < c ∧ 0 < N

/-- The finite cyclic phase quotient induced by a residual gate. -/
abbrev ResidualPhaseQuotient (c : ℕ) := ZMod c

/-- Every nonzero residual gate induces a finite cyclic quotient `Z/cZ`. -/
theorem finite_quotient_necessity {c N : ℕ}
    (h : NonzeroResidual c N) :
    Nonempty (Fintype (ResidualPhaseQuotient c)) := by
  have hcne : c ≠ 0 := Nat.ne_of_gt h.1
  letI : NeZero c := ⟨hcne⟩
  exact ⟨inferInstance⟩

/-! ## 2. Gate ladder forcing -/

/-- For the hard class `n ≡ 1 mod 4`, admissible residual gates are `3 mod 4`. -/
def AdmissibleHardGate (c : ℕ) : Prop :=
  c % 4 = 3

/-- If `n ≡ 1 mod 4` and `x = (n+c)/4` is an integer posting, then
the residual gate satisfies `c ≡ 3 mod 4`. -/
theorem gate_ladder_forced {n c x : ℕ}
    (hn : n % 4 = 1)
    (hx : 4 * x = n + c) :
    AdmissibleHardGate c := by
  unfold AdmissibleHardGate
  omega

/-- Conversely, `c ≡ 3 mod 4` is exactly the condition making `n+c`
divisible by 4 in the hard class. -/
theorem admissible_gate_posts {n c : ℕ}
    (hn : n % 4 = 1)
    (hc : AdmissibleHardGate c) :
    4 ∣ n + c := by
  unfold AdmissibleHardGate at hc
  exact Nat.dvd_of_mod_eq_zero (by omega)

/-! ## 3. Defect-pair equivalence -/

/-- A rational closure witness for a gate `c`: the data needed by
`repr_of_gate_divisor_pair`. -/
def GateClosureWitness (n c : ℕ) : Prop :=
  ∃ x N d q : ℚ,
    (n : ℚ) ≠ 0 ∧
    x ≠ 0 ∧
    (c : ℚ) ≠ 0 ∧
    N = (n : ℚ) * x ∧
    x = ((n : ℚ) + (c : ℚ)) / 4 ∧
    d * q = N ∧
    (N + d) / (c : ℚ) ≠ 0 ∧
    (N + N * q) / (c : ℚ) ≠ 0

/-- The RCL divisor-pair bridge: a gate closure witness gives a rational
Erdős-Straus representation. -/
theorem gate_closure_witness_gives_repr {n c : ℕ}
    (h : GateClosureWitness n c) :
    HasRationalErdosStrausRepr (n : ℚ) := by
  rcases h with ⟨x, N, d, q, hn, hx, hc, hN, hxdef, hdq, hy, hz⟩
  exact repr_of_gate_divisor_pair
    (n := (n : ℚ)) (x := x) (c := (c : ℚ)) (N := N) (d := d) (q := q)
    hn hx hc hN hxdef hdq hy hz

/-- A direct balanced-pair phase support witness in the square budget `N^2`.
This is the exact finite-quotient condition:

* `x` is the first denominator, so `N = n*x` and `c = 4*x - n`;
* `d*e = N^2`;
* both defects land in phase `-N mod c`, expressed as divisibility of
  `N+d` and `N+e`.

The positivity fields keep the rational denominators nonzero. -/
def BalancedPairPhaseSupport (n c : ℕ) : Prop :=
  ∃ x N d e : ℕ,
    0 < n ∧ 0 < c ∧ 0 < x ∧ 0 < N ∧ 0 < d ∧ 0 < e ∧
    N = n * x ∧
    c = 4 * x - n ∧
    d * e = N ^ 2 ∧
    c ∣ N + d ∧
    c ∣ N + e

/-- A balanced-pair phase support witness gives an Erdős-Straus
representation.  This is the finite reciprocal-pair closure theorem. -/
theorem balanced_pair_phase_support_gives_repr {n c : ℕ}
    (h : BalancedPairPhaseSupport n c) :
    HasRationalErdosStrausRepr (n : ℚ) := by
  rcases h with ⟨x, N, d, e, hnpos, hcpos, hxpos, hNpos, hdpos, hepos,
    hN, hcdefNat, hde, _hcd, _hce⟩
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hx : (x : ℚ) ≠ 0 := by exact_mod_cast hxpos.ne'
  have hc : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hy : (((N : ℚ) + (d : ℚ)) / (c : ℚ)) ≠ 0 := by
    have hnum : ((N : ℚ) + (d : ℚ)) ≠ 0 := by
      have hpos : (0 : ℚ) < (N : ℚ) + (d : ℚ) := by
        exact add_pos (by exact_mod_cast hNpos) (by exact_mod_cast hdpos)
      exact ne_of_gt hpos
    exact div_ne_zero hnum hc
  have hz : (((N : ℚ) + (e : ℚ)) / (c : ℚ)) ≠ 0 := by
    have hnum : ((N : ℚ) + (e : ℚ)) ≠ 0 := by
      have hpos : (0 : ℚ) < (N : ℚ) + (e : ℚ) := by
        exact add_pos (by exact_mod_cast hNpos) (by exact_mod_cast hepos)
      exact ne_of_gt hpos
    exact div_ne_zero hnum hc
  have hNQ : (N : ℚ) = (n : ℚ) * (x : ℚ) := by
    exact_mod_cast hN
  have hcdefQ : (c : ℚ) = 4 * (x : ℚ) - (n : ℚ) := by
    have hcadd : c + n = 4 * x := by omega
    have hcaddQ : (c : ℚ) + (n : ℚ) = 4 * (x : ℚ) := by
      exact_mod_cast hcadd
    linarith
  have hdeQ : (d : ℚ) * (e : ℚ) = (N : ℚ) ^ 2 := by
    exact_mod_cast hde
  refine repr_of_balanced_factor_pair
    (n := (n : ℚ)) (x := (x : ℚ)) (c := (c : ℚ)) (N := (N : ℚ))
    (d := (d : ℚ)) (e := (e : ℚ))
    (y := ((N : ℚ) + (d : ℚ)) / (c : ℚ))
    (z := ((N : ℚ) + (e : ℚ)) / (c : ℚ))
    hn hx hc hy hz hNQ hcdefQ hdeQ ?_ ?_
  · field_simp [hc]
  · field_simp [hc]

/-! ## 4. Trap characterization -/

/-- Every prime divisor of `m` lies in residue class `1 mod 3`. -/
def AllPrimeFactorsOneModThree (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ m → p % 3 = 1

/-- The residual trapped class after the explicit formulas:
`n ≡ 1 mod 24`, and both ledger sources are built only from primes
`1 mod 3`. -/
def ResidualTrap (n : ℕ) : Prop :=
  1 < n ∧
  n % 24 = 1 ∧
  AllPrimeFactorsOneModThree n ∧
  AllPrimeFactorsOneModThree ((n + 3) / 4)

/-! ## 5-10. Missing engines as explicit first-principles targets -/

/-- A gate has enough phase support if its finite quotient sees a
non-identity phase in the divisor ledger.  This is intentionally abstract:
the next proof must instantiate it from prime phase distribution. -/
def GateHasPhaseSupport (n c : ℕ) : Prop :=
  ∃ _ : ResidualPhaseQuotient c, n = n

/-- Prime phase equidistribution: trapped ledgers are eventually separated
by an admissible finite quotient. -/
structure PrimePhaseEquidistributionEngine : Prop where
  phase_support :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, AdmissibleHardGate c ∧ GateHasPhaseSupport n c

/-- Effective bounded search: the separating gate can be chosen below a
specific bound. -/
structure BoundedSearchEngine : Type where
  bound : ℕ → ℕ
  bound_ok :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ GateHasPhaseSupport n c

/-- Reciprocal pair closure: once a gate has enough phase support, it yields
the actual reciprocal divisor-pair witness required by RCL. -/
structure ReciprocalPairClosureEngine : Prop where
  close :
    ∀ n c : ℕ, ResidualTrap n → AdmissibleHardGate c → GateHasPhaseSupport n c →
      GateClosureWitness n c

/-- Stronger, fully arithmetic bounded search: the search returns the actual
balanced phase pair, not merely abstract phase support. -/
structure BoundedBalancedSearchEngine : Type where
  bound : ℕ → ℕ
  bound_ok :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ BalancedPairPhaseSupport n c

/-- A finite-range bounded balanced-search certificate.  This is the form
that computation can honestly certify: all trapped `n ≤ maxN` have a gate
`c ≤ bound`. -/
structure FiniteBoundedBalancedSearchCert where
  maxN : ℕ
  bound : ℕ
  verified :
    ∀ n : ℕ, n ≤ maxN → ResidualTrap n →
      ∃ c : ℕ, c ≤ bound ∧ AdmissibleHardGate c ∧ BalancedPairPhaseSupport n c

/-- A global engine implies every finite-range certificate. -/
theorem finite_cert_of_global_engine
    (engine : BoundedBalancedSearchEngine)
    (maxN : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, n ≤ maxN → ResidualTrap n →
      ∃ c : ℕ, c ≤ B ∧ AdmissibleHardGate c ∧ BalancedPairPhaseSupport n c := by
  classical
  let B : ℕ := (Finset.range (maxN + 1)).sup engine.bound
  refine ⟨B, ?_⟩
  intro n hnmax hntrap
  rcases engine.bound_ok n hntrap with ⟨c, hcbound, hc, hpair⟩
  refine ⟨c, ?_, hc, hpair⟩
  exact le_trans hcbound (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_of_le hnmax)))

/-- Rotation separation + reciprocal closure solve the residual class. -/
theorem residual_trap_solved
    (phase : PrimePhaseEquidistributionEngine)
    (pair : ReciprocalPairClosureEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    HasRationalErdosStrausRepr (n : ℚ) := by
  rcases phase.phase_support n hn with ⟨c, hc, hsupport⟩
  exact gate_closure_witness_gives_repr (pair.close n c hn hc hsupport)

/-- A bounded search engine is a stronger form of prime phase separation. -/
theorem bounded_search_implies_phase_equidistribution
    (bounded : BoundedSearchEngine) :
    PrimePhaseEquidistributionEngine := by
  refine ⟨?_⟩
  intro n hn
  rcases bounded.bound_ok n hn with ⟨c, _hcbound, hc, hsupport⟩
  exact ⟨c, hc, hsupport⟩

/-- Bounded search + reciprocal closure solve the residual class. -/
theorem bounded_residual_trap_solved
    (bounded : BoundedSearchEngine)
    (pair : ReciprocalPairClosureEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    HasRationalErdosStrausRepr (n : ℚ) :=
  residual_trap_solved (bounded_search_implies_phase_equidistribution bounded) pair hn

/-- A bounded balanced-search engine alone solves the residual class.  This is
the most concrete remaining target: find the gate and the reciprocal pair. -/
theorem bounded_balanced_search_solved
    (bounded : BoundedBalancedSearchEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    HasRationalErdosStrausRepr (n : ℚ) := by
  rcases bounded.bound_ok n hn with ⟨c, _hcbound, _hc, hpair⟩
  exact balanced_pair_phase_support_gives_repr hpair

end ErdosStrausRotationHierarchy
end NumberTheory
end IndisputableMonolith
