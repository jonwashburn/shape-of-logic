import Mathlib
import IndisputableMonolith.Gravity.LedgerSuperposition

/-!
# Gravity IV, Track 2.A: Macroscopic Ledger Hilbert Carrier (THEOREM)

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom).

This module discharges Track 2.A of the master plan: it upgrades the
"macroscopic ledger Hilbert carrier" from a definition / CONDITIONAL
THEOREM in paper IV to a Lean theorem that the recognition update extends
canonically and `ℂ`-linearly from the single-site `Signal8` carrier
(`LedgerSuperposition`) to a finite tensor product over an arbitrary
finite indexing set of sites.

## Construction

Given a finite indexing set `ι` of sites, the macroscopic ledger Hilbert
carrier is the `ι`-fold `PiTensorProduct` over `ℂ` of single-site
`Signal8` factors:

```
def MacroscopicLedger : Type :=
  ⨂[ℂ] _ : ι, Signal8
```

The recognition update on each factor is the linearization of
`cyclic_shift` (proved `ℂ`-linear in `LedgerSuperposition`); the
macroscopic recognition update is `PiTensorProduct.map` applied
factor-wise. By the universal property of `PiTensorProduct.map`, the
result is automatically `ℂ`-linear and acts on pure tensors `⨂ᵢ ψᵢ` by
`⨂ᵢ cyclic_shift ψᵢ`.

## Why this matters

Paper IV's Theorem 1 (Ledger Superposition) is unconditional for the
single-site carrier. The macroscopic claim — that ledger superpositions
of multi-site configurations are physical and preserved by recognition —
needs the same theorem at the tensor-product level. Track 2.A converts
that claim from CONDITIONAL THEOREM to STRUCTURAL THEOREM.

## What this does *not* do

This module formalises macroscopic ledger superposition at the
amplitude-linear level (the universal property of the tensor product).
It does not yet force the *physical* identification of the macroscopic
recognition update with the gravitational-channel response operator;
that is Track 2.C ("Force C2 from substrate"), which converts T2's MODEL
tag to THEOREM by ruling out classical-mediator extensions on the joint
matter-plus-channel Hilbert space.
-/

namespace IndisputableMonolith
namespace Gravity
namespace MacroscopicLedger

/-- Local abbreviation: the eight-tick analytic signal carrier, identified
with the canonical `Foundation.ComplexStructureForcing.Signal8`. -/
abbrev Signal8 : Type :=
  IndisputableMonolith.Foundation.ComplexStructureForcing.Signal8

/-- Local abbreviation: the one-tick recognition update on `Signal8`. -/
abbrev cyclic_shift : Signal8 → Signal8 :=
  IndisputableMonolith.Spectral.cyclic_shift

open scoped TensorProduct

noncomputable section

/-! ## §1. Single-site recognition update as a `ℂ`-linear map -/

/-- The single-site recognition update `cyclic_shift` packaged as a
`ℂ`-linear endomorphism of `Signal8`. Linearity (additivity and scalar
homogeneity) is from `cyclic_shift_add` and `cyclic_shift_smul`
in `Foundation.SchrodingerDerivation`. -/
def cyclicShiftLinear : Signal8 →ₗ[ℂ] Signal8 where
  toFun := cyclic_shift
  map_add' v w :=
    IndisputableMonolith.Foundation.SchrodingerDerivation.cyclic_shift_add v w
  map_smul' c v :=
    IndisputableMonolith.Foundation.SchrodingerDerivation.cyclic_shift_smul c v

@[simp] theorem cyclicShiftLinear_apply (ψ : Signal8) :
    cyclicShiftLinear ψ = cyclic_shift ψ := rfl

/-- The single-site update is `ℂ`-linear (paired with the
`LedgerSuperposition` superposition theorem). -/
theorem cyclicShiftLinear_map_add (ψ φ : Signal8) :
    cyclicShiftLinear (ψ + φ) = cyclicShiftLinear ψ + cyclicShiftLinear φ :=
  cyclicShiftLinear.map_add ψ φ

theorem cyclicShiftLinear_map_smul (c : ℂ) (ψ : Signal8) :
    cyclicShiftLinear (c • ψ) = c • cyclicShiftLinear ψ :=
  cyclicShiftLinear.map_smul c ψ

/-! ## §2. The macroscopic ledger carrier as a `PiTensorProduct` -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The macroscopic ledger Hilbert carrier over a finite indexing set
`ι` of sites: the `ι`-fold `PiTensorProduct` over `ℂ` of single-site
`Signal8` factors. The index type is in `Type` (universe 0) to keep the
universe constraints simple; `Fin n`, `Finset.univ`, and any concrete
finite site set fit. -/
abbrev MacroscopicLedger (ι : Type) [Fintype ι] [DecidableEq ι] : Type :=
  ⨂[ℂ] _ : ι, Signal8

/-- The macroscopic recognition update on the ledger Hilbert carrier:
the `PiTensorProduct.map` of the single-site `cyclicShiftLinear` on each
factor. By construction this is `ℂ`-linear. -/
noncomputable def MacroscopicShift :
    MacroscopicLedger ι →ₗ[ℂ] MacroscopicLedger ι :=
  PiTensorProduct.map (fun _ : ι => cyclicShiftLinear)

/-! ## §3. Action on pure tensors -/

/-- Action of the macroscopic recognition update on a pure tensor
configuration: `R̂_macro (⨂ᵢ ψᵢ) = ⨂ᵢ R̂ ψᵢ`. -/
theorem MacroscopicShift_tprod (ψ : ι → Signal8) :
    MacroscopicShift (PiTensorProduct.tprod ℂ ψ) =
      PiTensorProduct.tprod ℂ (fun i => cyclic_shift (ψ i)) := by
  unfold MacroscopicShift
  rw [PiTensorProduct.map_tprod]
  rfl

/-! ## §4. Linearity and superposition preservation -/

/-- **Linearity.** The macroscopic recognition update is `ℂ`-linear
(by construction, since `PiTensorProduct.map` returns a `LinearMap`).
This restates the universal property explicitly. -/
theorem MacroscopicShift_map_add (Ψ Φ : MacroscopicLedger ι) :
    MacroscopicShift (Ψ + Φ) = MacroscopicShift Ψ + MacroscopicShift Φ :=
  MacroscopicShift.map_add Ψ Φ

theorem MacroscopicShift_map_smul (c : ℂ) (Ψ : MacroscopicLedger ι) :
    MacroscopicShift (c • Ψ) = c • MacroscopicShift Ψ :=
  MacroscopicShift.map_smul c Ψ

/-- **Macroscopic ledger superposition.** For a finite family of
macroscopic ledger configurations `Ψ : κ → MacroscopicLedger ι` and
amplitudes `c : κ → ℂ` indexed by a finite set, the macroscopic
recognition update commutes with the finite linear combination. This is
the explicit superposition principle for multi-site ledger
configurations. -/
theorem MacroscopicShift_finite_sum
    {κ : Type*} (s : Finset κ) (c : κ → ℂ) (Ψ : κ → MacroscopicLedger ι) :
    MacroscopicShift (∑ α ∈ s, c α • Ψ α) =
      ∑ α ∈ s, c α • MacroscopicShift (Ψ α) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert α s hα ih =>
    rw [Finset.sum_insert hα, Finset.sum_insert hα,
        MacroscopicShift_map_add, MacroscopicShift_map_smul, ih]

/-! ## §5. Master certificate -/

/-- **MACROSCOPIC LEDGER HILBERT CARRIER CERTIFICATE.**

Five clauses establishing that the macroscopic ledger Hilbert carrier
is a `ℂ`-linear extension of the single-site recognition update:

1. `single_site_linear`: the single-site recognition update
   `cyclicShiftLinear` is a `ℂ`-linear map `Signal8 →ₗ[ℂ] Signal8`.
2. `tensor_action`: on a pure tensor configuration, the macroscopic
   update acts factor-wise.
3. `additive`: the macroscopic update is additive.
4. `scalar_homogeneous`: the macroscopic update is scalar-homogeneous.
5. `finite_superposition`: the macroscopic update commutes with finite
   linear combinations (the superposition principle for multi-site
   ledger configurations).

This discharges Track 2.A of the master plan: the macroscopic ledger
Hilbert carrier is now a STRUCTURAL THEOREM rather than a definition or
CONDITIONAL THEOREM. -/
structure MacroscopicLedgerTheorem (ι : Type) [Fintype ι] [DecidableEq ι] where
  /-- (1) Single-site update is a linear map. -/
  single_site_linear :
    ∀ (ψ φ : Signal8) (a b : ℂ),
      cyclicShiftLinear (a • ψ + b • φ) =
        a • cyclicShiftLinear ψ + b • cyclicShiftLinear φ
  /-- (2) Pure-tensor action: factor-wise. -/
  tensor_action :
    ∀ (ψ : ι → Signal8),
      MacroscopicShift (PiTensorProduct.tprod ℂ ψ) =
        PiTensorProduct.tprod ℂ (fun i => cyclic_shift (ψ i))
  /-- (3) Macroscopic update is additive. -/
  additive :
    ∀ (Ψ Φ : MacroscopicLedger ι),
      MacroscopicShift (Ψ + Φ) = MacroscopicShift Ψ + MacroscopicShift Φ
  /-- (4) Macroscopic update is scalar-homogeneous. -/
  scalar_homogeneous :
    ∀ (c : ℂ) (Ψ : MacroscopicLedger ι),
      MacroscopicShift (c • Ψ) = c • MacroscopicShift Ψ
  /-- (5) Macroscopic update commutes with finite superposition. -/
  finite_superposition :
    ∀ {κ : Type*} (s : Finset κ) (c : κ → ℂ) (Ψ : κ → MacroscopicLedger ι),
      MacroscopicShift (∑ α ∈ s, c α • Ψ α) =
        ∑ α ∈ s, c α • MacroscopicShift (Ψ α)

/-- The macroscopic ledger theorem is verified. -/
noncomputable def macroscopicLedgerTheorem
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    MacroscopicLedgerTheorem ι where
  single_site_linear ψ φ a b := by
    rw [cyclicShiftLinear.map_add, cyclicShiftLinear.map_smul,
        cyclicShiftLinear.map_smul]
  tensor_action := MacroscopicShift_tprod
  additive := MacroscopicShift_map_add
  scalar_homogeneous := MacroscopicShift_map_smul
  finite_superposition := MacroscopicShift_finite_sum

theorem macroscopicLedgerTheorem_inhabited
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    Nonempty (MacroscopicLedgerTheorem ι) :=
  ⟨macroscopicLedgerTheorem ι⟩

end

end MacroscopicLedger
end Gravity
end IndisputableMonolith
