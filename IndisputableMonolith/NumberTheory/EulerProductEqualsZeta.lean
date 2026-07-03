import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import IndisputableMonolith.NumberTheory.EulerLedgerPartition
import IndisputableMonolith.NumberTheory.LogicPrimeLedgerAtom

/-!
  EulerProductEqualsZeta.lean

  Phase 1 of the RS-native zeta program.

  This module wires the formal RS prime-ledger partition to Mathlib's
  theorem that the Euler product over primes equals the Riemann zeta function
  on the half-plane `Re(s) > 1`.

  The point is not to reprove analytic continuation here. The point is to
  replace the old `True` stub in `EulerLedgerPartitionCert` with a real
  analytic theorem: the Euler product over prime ledger atoms converges to
  `riemannZeta` in the domain where the product is classically valid.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace EulerProductEqualsZeta

open Filter Topology
open LogicPrimeLedgerAtom

noncomputable section

/-- The Mathlib Euler product theorem for `riemannZeta`, restated under the
RS prime-ledger namespace. This is the convergence of finite prime partial
products to `riemannZeta s` on `Re(s) > 1`. -/
theorem rs_riemannZeta_eulerProduct_tendsto (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹)
      atTop (𝓝 (riemannZeta s)) :=
  _root_.riemannZeta_eulerProduct hs

/-- The equivalent infinite-product statement. -/
theorem rs_riemannZeta_eulerProduct_tprod (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  _root_.riemannZeta_eulerProduct_tprod hs

/-- `HasProd` form of the same theorem. -/
theorem rs_riemannZeta_eulerProduct_hasProd (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  _root_.riemannZeta_eulerProduct_hasProd hs

/-- The finite prime-ledger partition is exactly Mathlib's finite Euler
partial product over `Nat.primesBelow n`. -/
theorem finitePrimeLedgerPartition_primesBelow (s : ℂ) (n : ℕ) :
    finitePrimeLedgerPartition s (Nat.primesBelow n) =
      ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  unfold finitePrimeLedgerPartition primeLedgerLocalPartition primePostingWeight
  apply Finset.prod_congr rfl
  intro p hp
  have hprime : Nat.Prime p := by
    exact (Nat.mem_primesBelow.mp hp).2
  simp [hprime]

/-- The RS finite prime-ledger partitions converge to `riemannZeta` on
`Re(s) > 1`. This is the ledger reading of Mathlib's Euler product theorem. -/
theorem ledger_partition_equals_zeta (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ finitePrimeLedgerPartition s (Nat.primesBelow n))
      atTop (𝓝 (riemannZeta s)) := by
  simpa [finitePrimeLedgerPartition_primesBelow] using
    rs_riemannZeta_eulerProduct_tendsto s hs

/-- The recovered-prime ledger is compatible with the analytic Euler product:
prime postings in the recovered ledger transport to the classical prime
factors used by Mathlib's Euler product. -/
theorem recovered_prime_ledger_supports_euler_product :
    PrimeLedgerLogicCert ∧
      (∀ s : ℂ, 1 < s.re →
        Tendsto (fun n : ℕ ↦ finitePrimeLedgerPartition s (Nat.primesBelow n))
          atTop (𝓝 (riemannZeta s))) :=
  ⟨primeLedgerLogicCert, ledger_partition_equals_zeta⟩

end

end EulerProductEqualsZeta
end NumberTheory
end IndisputableMonolith
