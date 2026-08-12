import IndisputableMonolith.Foundation.PairKernelLocality

/-!
# Door 2 / discrete Gauss: recognition flux, site-divergence = sigma-imbalance

Pair-kernel provenance lane (`glm/fold_derivation_logs/pairwise_kernel_derive.md`).

After the pair-cost carrier (`ShiftInvariant`, MODEL-terminal) and the locality hypothesis
(`FiniteRange`, HYPOTHESIS; atomic-tick provenance CLOSED NEGATIVE), the next vertebra is the
discrete Gauss / continuity law: the divergence of the recognition current equals the local
sigma-imbalance, and integrating over the lattice gives zero net source (the sigma = 0 conservation
law), with the regional form giving source-in-region = flux-through-boundary.

## The vacuity trap, and the null test built FIRST

The trap the lane flags explicitly: if one *defines* the current as a gradient `F i j := φ i − φ j`
and the source as the graph Laplacian `Δφ`, then "divergence = source" is the identity
`Δφ = div (∇φ)` — a tautology that says nothing about double-entry and carries no conservation
content (it holds for every `φ`). So the flux is kept ABSTRACT here: `F : Fin n → Fin n → ℝ` is a
free antisymmetric current, never `∇φ`. The real content is CONSERVATION, and it holds *because* the
current is antisymmetric (`F i j = − F j i`), which is exactly the double-entry structure of a
recognition event (each debit at one account is a matching credit at another).

Reviewer vacuity check, run before the theorems: is global conservation `∑ divF = 0` a null test
(true for every flow)? No. `constFlow_breaks_conservation` shows a non-antisymmetric flow
(`F ≡ 1`) has `∑ divF = n² ≠ 0`. So antisymmetry is load-bearing; the Gauss law has teeth. This is
the null test built first, and it passes (instrument informative).

## What is proved (all axiom-clean)

- `antisym_sum_finset_zero`: over any region `S`, an antisymmetric current sums to zero
  (`∑_{i∈S} ∑_{j∈S} F i j = 0`). The double-entry cancellation, the engine of everything below.
- `sum_divF_zero` (**global Gauss**): `∑ i, divF F i = 0`. Net recognition source over the whole
  lattice is zero — the sigma = 0 neutrality, forced by antisymmetry.
- `sum_divF_region_eq_boundary_flux` (**regional Gauss / divergence theorem**):
  `∑_{i∈S} divF F i = ∑_{i∈S} ∑_{j∈Sᶜ} F i j`. Source in a region equals flux through its boundary.
  This is the genuine (non-tautological) discrete divergence theorem: it holds for ANY antisymmetric
  current, gradient or not, so it is not a statement about `∇φ`.
- `sigma_sum_zero_of_continuity`: if a source `sigma` satisfies the continuity law `divF F = sigma`
  for an antisymmetric current, then `∑ sigma = 0`. This is "site-divergence = sigma-imbalance ⇒
  global sigma neutrality" without ever writing `sigma := Δφ`.
- `elementaryPosting` + `_antisym` + `_sum_div_zero` + `_div_source`: the double-entry witness — a
  single a→b posting is an antisymmetric current whose divergence is `+1` at `a` and `−1` at `b`
  (the concrete debit/credit source), and it conserves globally.
- Decoy `constFlow` + `constFlow_not_antisym` + `constFlow_breaks_conservation`: the null test.

## Scoped verdict (`inference-discipline.mdc` form)

- CLAIM: for any antisymmetric recognition current on a finite lattice, the divergence obeys the
  discrete Gauss law (global net source zero; regional source = boundary flux), and a source it
  realizes is globally neutral. Antisymmetry (double-entry) is necessary (`constFlow` decoy).
- DOMAIN: currents `F : Fin n → Fin n → ℝ`; `divF F i = ∑ j, F i j`; regions `S : Finset (Fin n)`.
- PREMISES: `IsAntisym F` (double-entry) [the modelled structure of a recognition event; a single
  posting realizes it, `elementaryPosting_antisym`].
- REACH: max licensed → "the recognition current obeys a genuine discrete Gauss law; global sigma is
  conserved by double-entry; source in a region = boundary flux." Does NOT license → `1/r` from this
  alone (that is L4, the Green's function of the resulting Laplacian), nor that the current is a
  gradient (`F` is free antisymmetric), nor any use of `5/8`, `5/16`, `27/16`, `Z_eff`, hydrogenic
  `F(r)` (none appear here).

Zero `sorry`. Zero new `axiom`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PairKernelDiscreteGauss

open Finset

noncomputable section

/-! ## §1. The recognition current and its divergence -/

/-- **Double-entry structure.** A recognition current is antisymmetric: the flow from `i` to `j` is
    minus the flow from `j` to `i`. This is exactly what "every debit has a matching credit" means
    at the level of the elementary current. It is NOT the gradient condition; a gradient
    `F i j = φ i − φ j` is one instance, but the theorems below use only antisymmetry. -/
def IsAntisym {n : ℕ} (F : Fin n → Fin n → ℝ) : Prop := ∀ i j, F i j = - F j i

/-- Site divergence: the net recognition outflow from site `i`. -/
def divF {n : ℕ} (F : Fin n → Fin n → ℝ) (i : Fin n) : ℝ := ∑ j : Fin n, F i j

/-! ## §2. Null test (built first): antisymmetry is load-bearing

The uniform current `F ≡ 1` is NOT antisymmetric, and it does NOT conserve: `∑ divF = n²`. So the
global Gauss law below is not a null test — deleting the antisymmetry hypothesis lets a
non-conserving flow stand. -/

/-- The uniform (all-ones) current — a decoy that is not double-entry. -/
def constFlow (n : ℕ) : Fin n → Fin n → ℝ := fun _ _ => 1

theorem constFlow_not_antisym (n : ℕ) (hn : 0 < n) : ¬ IsAntisym (constFlow n) := by
  intro h
  have hii := h ⟨0, hn⟩ ⟨0, hn⟩
  simp only [constFlow] at hii
  norm_num at hii

theorem constFlow_sum_div (n : ℕ) :
    ∑ i : Fin n, divF (constFlow n) i = (n : ℝ) * (n : ℝ) := by
  simp only [divF, constFlow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- **Null test passes.** A non-antisymmetric current breaks global conservation
    (`∑ divF ≠ 0`). So the double-entry hypothesis is load-bearing in the Gauss law. -/
theorem constFlow_breaks_conservation (n : ℕ) (hn : 0 < n) :
    ∑ i : Fin n, divF (constFlow n) i ≠ 0 := by
  rw [constFlow_sum_div]
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact (mul_pos hpos hpos).ne'

/-! ## §3. The double-entry cancellation, over an arbitrary region -/

/-- Over any region `S`, an antisymmetric current sums to zero: the double-entry cancellation.
    This is the engine of both the global and regional Gauss laws. -/
theorem antisym_sum_finset_zero {n : ℕ} {F : Fin n → Fin n → ℝ} (h : IsAntisym F)
    (S : Finset (Fin n)) : ∑ i ∈ S, ∑ j ∈ S, F i j = 0 := by
  have hcomm : (∑ i ∈ S, ∑ j ∈ S, F j i) = ∑ i ∈ S, ∑ j ∈ S, F i j := Finset.sum_comm
  have hzero : (∑ i ∈ S, ∑ j ∈ S, (F i j + F j i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have := h i j
    linarith
  have hsplit : (∑ i ∈ S, ∑ j ∈ S, (F i j + F j i))
      = (∑ i ∈ S, ∑ j ∈ S, F i j) + (∑ i ∈ S, ∑ j ∈ S, F j i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_add_distrib]
  rw [hsplit, hcomm] at hzero
  linarith

/-! ## §4. Global and regional discrete Gauss -/

/-- **Global discrete Gauss.** The total recognition source over the whole lattice is zero: the
    sigma = 0 conservation law, forced by double-entry antisymmetry (not by any `φ`). -/
theorem sum_divF_zero {n : ℕ} {F : Fin n → Fin n → ℝ} (h : IsAntisym F) :
    ∑ i : Fin n, divF F i = 0 := by
  simp only [divF]
  simpa using antisym_sum_finset_zero h (Finset.univ)

/-- **Regional discrete Gauss (divergence theorem).** Source in a region `S` equals the flux
    through its boundary: `∑_{i∈S} divF F i = ∑_{i∈S} ∑_{j∈Sᶜ} F i j`. Holds for ANY antisymmetric
    current — gradient or circulating — so it is not a statement about `∇φ`. -/
theorem sum_divF_region_eq_boundary_flux {n : ℕ} {F : Fin n → Fin n → ℝ} (h : IsAntisym F)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, divF F i = ∑ i ∈ S, ∑ j ∈ Sᶜ, F i j := by
  have hsplit : ∀ i, divF F i = (∑ j ∈ S, F i j) + (∑ j ∈ Sᶜ, F i j) := by
    intro i
    rw [divF, ← Finset.sum_add_sum_compl S (fun j => F i j)]
  calc ∑ i ∈ S, divF F i
      = ∑ i ∈ S, ((∑ j ∈ S, F i j) + (∑ j ∈ Sᶜ, F i j)) := by
        apply Finset.sum_congr rfl; intro i _; exact hsplit i
    _ = (∑ i ∈ S, ∑ j ∈ S, F i j) + (∑ i ∈ S, ∑ j ∈ Sᶜ, F i j) := by
        rw [Finset.sum_add_distrib]
    _ = 0 + (∑ i ∈ S, ∑ j ∈ Sᶜ, F i j) := by rw [antisym_sum_finset_zero h S]
    _ = ∑ i ∈ S, ∑ j ∈ Sᶜ, F i j := by rw [zero_add]

/-- **Continuity ⇒ global neutrality.** If a source `sigma` is the divergence of an antisymmetric
    current (`divF F = sigma`, the Gauss law "site-divergence = sigma-imbalance"), then the total
    source is zero. This is the sigma = 0 conservation law stated on the source, with no `sigma :=
    Δφ` definitional shortcut. -/
theorem sigma_sum_zero_of_continuity {n : ℕ} {F : Fin n → Fin n → ℝ} {sigma : Fin n → ℝ}
    (h : IsAntisym F) (hcont : ∀ i, divF F i = sigma i) :
    ∑ i : Fin n, sigma i = 0 := by
  have : ∑ i : Fin n, sigma i = ∑ i : Fin n, divF F i := by
    apply Finset.sum_congr rfl
    intro i _
    exact (hcont i).symm
  rw [this, sum_divF_zero h]

/-! ## §5. The double-entry witness: a single posting is an antisymmetric current -/

/-- The elementary current of a single recognition posting from account `a` to account `b`:
    `+1` on the ordered pair `(a,b)`, `−1` on `(b,a)`, `0` elsewhere. This is the double-entry
    structure of one recognition event, built from postings, NOT from a potential. -/
def elementaryPosting {n : ℕ} (a b : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => (if i = a ∧ j = b then (1 : ℝ) else 0) - (if i = b ∧ j = a then (1 : ℝ) else 0)

theorem elementaryPosting_antisym {n : ℕ} (a b : Fin n) : IsAntisym (elementaryPosting a b) := by
  intro i j
  unfold elementaryPosting
  have c1 : (j = b ∧ i = a) ↔ (i = a ∧ j = b) := and_comm
  have c2 : (j = a ∧ i = b) ↔ (i = b ∧ j = a) := and_comm
  simp only [c1, c2]
  ring

/-- A single posting conserves globally (it is antisymmetric). -/
theorem elementaryPosting_sum_div_zero {n : ℕ} (a b : Fin n) :
    ∑ i : Fin n, divF (elementaryPosting a b) i = 0 :=
  sum_divF_zero (elementaryPosting_antisym a b)

/-- The divergence of the elementary a→b posting is `+1` at the source `a` (for `a ≠ b`): the
    concrete debit at `a`. Together with the `−1` at `b` this is the sigma-imbalance the current
    carries — the double-entry source, read off the postings, not off `∇φ`. -/
theorem elementaryPosting_div_source {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    divF (elementaryPosting a b) a = 1 := by
  have hstep : ∀ j : Fin n,
      elementaryPosting a b a j = (if j = b then (1 : ℝ) else 0) := by
    intro j
    simp only [elementaryPosting]
    have hb : (a = b ∧ j = a) → False := fun hc => hab hc.1
    rw [if_neg hb]
    simp only [true_and, sub_zero]
  calc divF (elementaryPosting a b) a
      = ∑ j : Fin n, elementaryPosting a b a j := rfl
    _ = ∑ j : Fin n, (if j = b then (1 : ℝ) else 0) := by
          exact Finset.sum_congr rfl (fun j _ => hstep j)
    _ = 1 := by simp

theorem elementaryPosting_div_sink {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    divF (elementaryPosting a b) b = -1 := by
  have hstep : ∀ j : Fin n,
      elementaryPosting a b b j = (if j = a then (-1 : ℝ) else 0) := by
    intro j
    simp only [elementaryPosting]
    have ha : (b = a ∧ j = b) → False := fun hc => hab hc.1.symm
    rw [if_neg ha]
    by_cases hja : j = a
    · subst hja; simp
    · simp [hja]
  calc divF (elementaryPosting a b) b
      = ∑ j : Fin n, elementaryPosting a b b j := rfl
    _ = ∑ j : Fin n, (if j = a then (-1 : ℝ) else 0) := by
          exact Finset.sum_congr rfl (fun j _ => hstep j)
    _ = -1 := by simp

/-- The divergence of an elementary posting is exactly the independently defined unit dipole.
    This identifies the recognition-current source with the source used by the finite
    Dirichlet action, including the degenerate case `a = b`. -/
theorem elementaryPosting_divF_eq_unitDipole {n : ℕ} (a b i : Fin n) :
    divF (elementaryPosting a b) i =
      SimplicialLedger.ContinuumBridge.unitDipole a b i := by
  unfold divF elementaryPosting SimplicialLedger.ContinuumBridge.unitDipole
  have hforward :
      (∑ j : Fin n, if i = a ∧ j = b then (1 : ℝ) else 0) =
        if i = a then 1 else 0 := by
    by_cases hia : i = a
    · subst i
      simp
    · simp [hia]
  have hbackward :
      (∑ j : Fin n, if i = b ∧ j = a then (1 : ℝ) else 0) =
        if i = b then 1 else 0 := by
    by_cases hib : i = b
    · subst i
      simp
    · simp [hib]
  rw [Finset.sum_sub_distrib, hforward, hbackward]

end

end PairKernelDiscreteGauss
end Foundation
end IndisputableMonolith
