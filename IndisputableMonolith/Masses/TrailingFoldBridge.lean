import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Masses.LeptonTorsionKernel
import IndisputableMonolith.Spectral.DFT8

/-!
# Trailing Fold Bridge (Target T1)

This module carries the honest two-layer landing for the trailing `φ/2` fold-debit
numerator of the charged-lepton torsion law, mirroring the L1 leading bridge in
`LeptonTorsionKernel`. T1 concerns only the **numerator** `φ/2`; the span/denominator
`Δr_32 = F = 6` is a separate object already forced in `SectorDependentTorsion`.

## The panel-vetted split (anti-circularity)

The bare statement `trailingFoldDebit = φ/2` is a definition, not a derivation. The
honest content is a forcing chain from two explicit physical premises to the proven
arithmetic value:

- **THEOREM layer (proved here, no `sorry`, axiom-clean arithmetic):**
  * `jCost_eq_half_iff` — the root-set certificate: for `x ≠ 0`, the recognition cost
    `J(x) = 1/2` **iff** `x ∈ {φ², φ⁻²}`. This is what makes premise B1 non-circular:
    the physical input is the *cost* `1/2`, and the golden ratio `φ²` is *forced out*,
    not assumed in.
  * `octave_half_period` — the 8-tick octave anchor `ω⁴ = -1` (re-exported from
    `Spectral.DFT8`): the half-period / Nyquist self-conjugate mode is mode 4 of the
    cycle length 8, giving the "octave" its literal referent.
  * `foldDebitNumerator_forced` — the CONDITIONAL forcing theorem
    `B1 ∧ B2 ⇒ numerator = φ/2`, resting on the already-proved `φ · J(φ²) = φ/2`.

- **MODEL layer (explicit `Prop` premises, NOT proved; the irreducible physical input):**
  * `OctaveClosurePremise ρ` (B1): the generation-cycle-closing fold conjugates
    recognition states across a ratio `ρ` whose recognition cost is the octave
    half-period cost `1/2`. Given `ρ ≠ 0`, this is equivalent to `ρ ∈ {φ², φ⁻²}`.
  * `SingleGoldenScalePremise p` (B2): the fold debit carries exactly one golden-ladder
    scale factor `φ¹`, paid once per generation-cycle closure (hence numerator is
    sector-independent and the span distributes it).

## Honest status

CONDITIONAL forcing THEOREM (B1 ∧ B2 ⇒ φ/2) + MODEL premises B1, B2. Same tier as the
L1 leading bridge. The open research bet (recorded, NOT closed): derive B1 — that the
generation-cycle-closing fold's recognition cost is exactly `1/2` — from the DFT-8
octave structure (`ω⁴ = -1`, phase half-period 4/8) rather than assuming it. The bridge
between the *phase-space* half-period `4/8` and the *cost-space* value `J = 1/2` is the
MODEL content of B1 and is currently unproved.

Lean status: no `sorry`; no new axioms beyond Mathlib base.
-/

namespace IndisputableMonolith
namespace Masses
namespace TrailingFoldBridge

open Constants
open LeptonTorsionKernel

noncomputable section

/-! ## THEOREM layer: the root-set certificate for the octave cost `1/2` -/

/-- **Root-set certificate.** For any nonzero `x`, the recognition cost `J(x)` equals the
octave half-cost `1/2` **iff** `x` is the golden square `φ²` or its inverse `φ⁻²`.

This is the panel-greenlit first step and the anti-circularity linchpin of T1: the
physical premise B1 supplies only the *cost* `1/2`; the golden ratio is a *consequence*.
The two roots are exactly the octave-conjugate pair (`φ² · φ⁻² = 1`, `φ² + φ⁻² = L₂ = 3`,
the 2nd Lucas number), consistent with `J`'s inversion symmetry `J(x) = J(x⁻¹)`. -/
theorem jCost_eq_half_iff {x : ℝ} (hx : x ≠ 0) :
    Cost.Jcost x = 1 / 2 ↔ x = phi ^ 2 ∨ x = phi⁻¹ ^ 2 := by
  have hφ2pos : 0 < phi ^ 2 := pow_pos Constants.phi_pos 2
  have hφ2 : phi ^ 2 ≠ 0 := ne_of_gt hφ2pos
  have hxx : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  -- The octave-conjugate pair: product `1`, sum `L₂ = 3`.
  have hprod : phi ^ 2 * phi⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ phi_ne_zero, one_pow]
  have hsum : phi ^ 2 + phi⁻¹ ^ 2 = 3 := by
    have hid : phi ^ 2 * (phi ^ 2 + phi⁻¹ ^ 2) = phi ^ 2 * 3 := by
      have expand : phi ^ 2 * (phi ^ 2 + phi⁻¹ ^ 2)
          = phi ^ 2 * phi ^ 2 + phi ^ 2 * phi⁻¹ ^ 2 := by ring
      rw [expand, hprod]
      linear_combination (phi ^ 2 + phi - 1) * phi_sq_eq
    exact mul_left_cancel₀ hφ2 hid
  constructor
  · intro h
    -- `J(x) = 1/2` clears to the quadratic `x² - 3x + 1 = 0`.
    have h3 : x + x⁻¹ = 3 := by
      unfold Cost.Jcost at h; linarith
    have hkey : x * (x + x⁻¹) = x * 3 := by rw [h3]
    rw [mul_add, hxx] at hkey
    have hquad : x ^ 2 - 3 * x + 1 = 0 := by linear_combination hkey
    -- Factor `x² - 3x + 1 = (x - φ²)(x - φ⁻²)` using the conjugate pair.
    have hfac : (x - phi ^ 2) * (x - phi⁻¹ ^ 2) = x ^ 2 - 3 * x + 1 := by
      linear_combination (-x) * hsum + hprod
    have hzero : (x - phi ^ 2) * (x - phi⁻¹ ^ 2) = 0 := by rw [hfac, hquad]
    rcases mul_eq_zero.mp hzero with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (sub_eq_zero.mp h2)
  · intro h
    rcases h with h1 | h2
    · rw [h1]; exact jCost_phi_sq_eq_half
    · rw [h2, inv_pow, ← Cost.Jcost_symm hφ2pos]
      exact jCost_phi_sq_eq_half

/-- **8-tick octave anchor.** The half-period (Nyquist) mode of the 8-tick recognition
cycle is mode 4: `ω⁴ = -1`. Mode index 4 over cycle length 8 is the phase-space "half".
This re-export gives the word "octave" in premise B1 a real referent. It does NOT by
itself equate the phase-space half-period `4/8` with the recognition cost `1/2`; that
identification is the MODEL content of B1 (the open research bet). -/
theorem octave_half_period : Spectral.omega8 ^ 4 = -1 := Spectral.omega8_pow_4

/-! ## MODEL layer: the two explicit physical premises (NOT proved) -/

/-- **MODEL premise B1 (octave closure).** The generation-cycle-closing fold conjugates
recognition states across a ratio `ρ` whose recognition cost is the octave half-period
cost `1/2`. This is the irreducible physical input; by `jCost_eq_half_iff` it forces
`ρ ∈ {φ², φ⁻²}`, so it does NOT assume the golden ratio, it assumes the octave cost. -/
def OctaveClosurePremise (rho : ℝ) : Prop :=
  Cost.Jcost rho = 1 / 2

/-- **MODEL premise B2 (single golden scale).** The fold debit carries exactly one
golden-ladder scale factor `φ¹`, paid once per generation-cycle closure. -/
def SingleGoldenScalePremise (prefactor : ℝ) : Prop :=
  prefactor = phi

/-- The trailing fold-debit numerator built from a prefactor and a fold ratio via the
recognition cost. This is the physical functional whose value T1 must land. -/
def foldDebitNumerator (prefactor rho : ℝ) : ℝ :=
  prefactor * Cost.Jcost rho

/-! ## THEOREM layer: the conditional forcing chain -/

/-- Given the octave-closure premise B1, the fold ratio is forced to the golden square
(up to inversion). This is the substantive non-circular content: `cost = 1/2` pins the
ratio, the ratio does not define the cost. -/
theorem octaveClosure_forces_golden_ratio
    {rho : ℝ} (hrho : rho ≠ 0) (hB1 : OctaveClosurePremise rho) :
    rho = phi ^ 2 ∨ rho = phi⁻¹ ^ 2 :=
  (jCost_eq_half_iff hrho).mp hB1

/-- **CONDITIONAL forcing theorem (T1).** The octave-closure premise B1 and the
single-golden-scale premise B2 together force the trailing fold-debit numerator to be
exactly `φ/2`. The proof rests on the already-proved arithmetic core `φ · J(φ²) = φ/2`
(`terminalFoldKernel_eq_phi_half`); B1 supplies `J = 1/2`, B2 supplies the prefactor `φ`. -/
theorem foldDebitNumerator_forced
    {prefactor rho : ℝ}
    (hB1 : OctaveClosurePremise rho)
    (hB2 : SingleGoldenScalePremise prefactor) :
    foldDebitNumerator prefactor rho = phi / 2 := by
  have hB1' : Cost.Jcost rho = 1 / 2 := hB1
  have hB2' : prefactor = phi := hB2
  unfold foldDebitNumerator
  rw [hB1', hB2']; ring

/-- The forced numerator is definitionally the proven `terminalFoldKernel` when the
premises are instantiated at their canonical witnesses `(prefactor, ρ) = (φ, φ²)`. This
ties the abstract forcing theorem to the concrete lake-checked `φ/2` anchor. -/
theorem foldDebitNumerator_at_golden :
    foldDebitNumerator phi (phi ^ 2) = terminalFoldKernel := rfl

/-! ## Certificate bundling the honest layers -/

/-- THEOREM-grade certificate for the parts of T1 that are proved. The two MODEL premises
`OctaveClosurePremise` / `SingleGoldenScalePremise` are deliberately NOT fields here: they
are the irreducible physical inputs the certificate is conditional on, exposed only
through the forcing implication. -/
structure TrailingFoldBridgeCert where
  root_set :
    ∀ {x : ℝ}, x ≠ 0 →
      (Cost.Jcost x = 1 / 2 ↔ x = phi ^ 2 ∨ x = phi⁻¹ ^ 2)
  octave_anchor :
    Spectral.omega8 ^ 4 = -1
  ratio_forced :
    ∀ {rho : ℝ}, rho ≠ 0 → OctaveClosurePremise rho →
      rho = phi ^ 2 ∨ rho = phi⁻¹ ^ 2
  numerator_forced :
    ∀ {prefactor rho : ℝ},
      OctaveClosurePremise rho → SingleGoldenScalePremise prefactor →
      foldDebitNumerator prefactor rho = phi / 2
  terminal_matches :
    foldDebitNumerator phi (phi ^ 2) = terminalFoldKernel

theorem trailingFoldBridgeCert_holds : Nonempty TrailingFoldBridgeCert :=
  ⟨{ root_set := fun hx => jCost_eq_half_iff hx
     octave_anchor := octave_half_period
     ratio_forced := fun hrho hB1 => octaveClosure_forces_golden_ratio hrho hB1
     numerator_forced := fun hB1 hB2 => foldDebitNumerator_forced hB1 hB2
     terminal_matches := foldDebitNumerator_at_golden }⟩

end

end TrailingFoldBridge
end Masses
end IndisputableMonolith
