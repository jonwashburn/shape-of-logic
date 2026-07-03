import Mathlib
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import IndisputableMonolith.NumberTheory.PrimeLedgerAtom

/-!
# Euler Ledger Partition

This module packages the Euler product as the partition function of independent
prime-ledger postings.

The finite product statements are proved directly.  The infinite equality with
`riemannZeta` is isolated in `EulerLedgerPartitionCert`, because the exact
Mathlib Euler-product API is an analytic import boundary rather than RS
structure.
-/

namespace IndisputableMonolith
namespace NumberTheory

open scoped Topology

noncomputable section

/-- One prime posting weighted at complex scale `s`. -/
def primePostingWeight (s : ℂ) (p : ℕ) : ℂ :=
  (p : ℂ) ^ (-s)

/-- Local geometric partition attached to one prime ledger atom. -/
def primeLedgerLocalPartition (s : ℂ) (p : ℕ) : ℂ :=
  (1 - primePostingWeight s p)⁻¹

/-- A finite prime-ledger partition over a finite set of primes. -/
def finitePrimeLedgerPartition (s : ℂ) (S : Finset ℕ) : ℂ :=
  ∏ p ∈ S, if Nat.Prime p then primeLedgerLocalPartition s p else 1

/-- Finite prime-ledger partition is insensitive to non-prime entries. -/
theorem finitePrimeLedgerPartition_insert_nonprime
    (s : ℂ) (S : Finset ℕ) {n : ℕ} (hnS : n ∉ S) (hn : ¬ Nat.Prime n) :
    finitePrimeLedgerPartition s (insert n S) = finitePrimeLedgerPartition s S := by
  unfold finitePrimeLedgerPartition
  simp [hnS, hn]

/-- Inserting a new prime multiplies the partition by its local factor. -/
theorem finitePrimeLedgerPartition_insert_prime
    (s : ℂ) (S : Finset ℕ) {p : ℕ} (hpS : p ∉ S) (hp : Nat.Prime p) :
    finitePrimeLedgerPartition s (insert p S) =
      primeLedgerLocalPartition s p * finitePrimeLedgerPartition s S := by
  unfold finitePrimeLedgerPartition
  simp [hpS, hp]

/-- The Euler ledger partition as a formal infinite product over prime atoms. -/
def PrimeLedgerPartition (s : ℂ) : Prop :=
  ∃ F : (Finset ℕ → ℂ), ∀ S, F S = finitePrimeLedgerPartition s S

/-- The formal partition exists, by finite partial products. -/
theorem primeLedgerPartition_formal (s : ℂ) : PrimeLedgerPartition s :=
  ⟨fun S => finitePrimeLedgerPartition s S, fun _ => rfl⟩

/-- Analytic certificate connecting the formal prime-ledger partition to zeta
on a convergence domain. -/
structure EulerLedgerPartitionCert where
  /-- Euler product agrees with `riemannZeta` for `Re(s) > 1`, expressed as
  convergence of finite prime-ledger partitions. -/
  eulerProduct_eq_zeta :
    ∀ s : ℂ, 1 < s.re →
      Filter.Tendsto (fun n : ℕ ↦ finitePrimeLedgerPartition s (Nat.primesBelow n))
        Filter.atTop (𝓝 (riemannZeta s))
  /-- The formal prime-ledger partition exists at every complex scale. -/
  formal_partition : ∀ s : ℂ, PrimeLedgerPartition s
  /-- Primes are exactly the ledger atoms. -/
  prime_atoms : PrimeLedgerCert

/-- The structural Euler ledger certificate.  The analytic equality field now
uses Mathlib's Euler-product theorem for `riemannZeta` on `Re(s) > 1`; the
finite products are exactly the finite prime-ledger partitions. -/
def eulerLedgerPartitionCert : EulerLedgerPartitionCert where
  eulerProduct_eq_zeta := by
    intro s hs
    have hmathlib :
        Filter.Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹)
          Filter.atTop (𝓝 (riemannZeta s)) :=
      _root_.riemannZeta_eulerProduct hs
    have hpart : (fun n : ℕ ↦ finitePrimeLedgerPartition s (Nat.primesBelow n)) =
        (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-s))⁻¹) := by
      funext n
      unfold finitePrimeLedgerPartition primeLedgerLocalPartition primePostingWeight
      apply Finset.prod_congr rfl
      intro p hp
      have hprime : Nat.Prime p := (Nat.mem_primesBelow.mp hp).2
      simp [hprime]
    simpa [hpart] using hmathlib
  formal_partition := primeLedgerPartition_formal
  prime_atoms := primeLedgerCert

end

end NumberTheory
end IndisputableMonolith
