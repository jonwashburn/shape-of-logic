import Mathlib
import IndisputableMonolith.Cost

/-!
# A Recognition-Cost Candidate for the Hilbert--Pólya Operator

The Hilbert--Pólya conjecture (Hilbert, Pólya, c. 1914) proposes that the
imaginary parts `γ_n` of the non-trivial zeros `ρ_n = 1/2 + i γ_n` of the
Riemann zeta function are eigenvalues of some self-adjoint operator on
a Hilbert space.  Such an operator's existence would prove RH.

This module constructs the algebraic skeleton of a candidate operator
on the free `ℝ`-module on the multiplicative group `ℚ_{>0}^×` (which is
the free abelian group on the primes), built from the Recognition Science
cost function `J`.  The reciprocal symmetry `J(x) = J(1/x)` translates
into an operator-level intertwining with the multiplicative involution
`q ↦ 1/q`, mirroring the zeta functional equation `ξ(s) = ξ(1-s)`.

We do NOT prove that the spectrum is the imaginary parts of zeta zeros.
That is the Hilbert--Pólya conjecture.  We construct the candidate
operator, prove its structural symmetries, and identify the open
spectral question.

## Main definitions

* `MultIndex`        : `Nat.Primes →₀ ℤ`, the multiplicative index space
                       (free abelian group on primes, isomorphic to
                       `ℚ_{>0}^×`).
* `toRat`            : `MultIndex → ℝ`, the rational `∏ p^(v p)`.
* `costAt`           : `MultIndex → ℝ`, the J-cost at a rational.
* `StateSpace`       : `MultIndex →₀ ℝ`, the free `ℝ`-module that
                       serves as our pre-Hilbert space.
* `diagOp`           : the diagonal cost operator `D`.
* `shiftOp p`        : the prime-shift operator `V_p`.
* `involutionOp`     : the reciprocal-involution operator `U`.

## Main theorems (all 0 sorry)

* `costAt_neg_eq`           : `J(1/q) = J(q)` at the index level.
* `involutionOp_involutive` : `U^2 = id`.
* `involutionOp_diagOp_comm`: `U ∘ D = D ∘ U`.
* `involutionOp_shiftOp`    : `U ∘ V_p = V_p^{-1} ∘ U`.
* `shiftOp_invertible`      : `V_p ∘ V_p^{-1} = id` (formal unitarity).

## Lean status: 0 sorry
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace HilbertPolyaCandidate

open Cost Finsupp

noncomputable section

/-! ## The multiplicative index space -/

/-- Index for the multiplicative group `ℚ_{>0}^×`: a finitely-supported
    function from primes to integers. -/
abbrev MultIndex : Type := Nat.Primes →₀ ℤ

/-- The positive rational corresponding to a multiplicative index,
    interpreted as a real number: `toRat v = ∏ p^(v p)`. -/
def toRat (v : MultIndex) : ℝ :=
  v.prod (fun p k => (p.val : ℝ) ^ (k : ℤ))

/-- The cost evaluated at the rational represented by `v`. -/
def costAt (v : MultIndex) : ℝ := Jcost (toRat v)

@[simp] theorem toRat_zero : toRat (0 : MultIndex) = 1 := by
  simp [toRat]

theorem toRat_pos (v : MultIndex) : 0 < toRat v := by
  unfold toRat
  rw [Finsupp.prod]
  apply Finset.prod_pos
  intro p _
  apply zpow_pos
  exact_mod_cast p.prop.pos

theorem toRat_add (v w : MultIndex) :
    toRat (v + w) = toRat v * toRat w := by
  unfold toRat
  rw [Finsupp.prod_add_index]
  · intro p _
    simp
  · intro p _ k₁ k₂
    rw [zpow_add₀ (by
      have hp : p.val ≠ 0 := Nat.Prime.ne_zero p.prop
      exact_mod_cast hp)]

theorem toRat_neg (v : MultIndex) : toRat (-v) = (toRat v)⁻¹ := by
  have h_sum : toRat ((-v) + v) = toRat (-v) * toRat v := toRat_add (-v) v
  have h_zero : ((-v) + v) = (0 : MultIndex) := by simp
  rw [h_zero, toRat_zero] at h_sum
  have hv_pos : 0 < toRat v := toRat_pos v
  have hv_ne : toRat v ≠ 0 := ne_of_gt hv_pos
  field_simp [hv_ne]
  linarith [h_sum]

/-- Reciprocal symmetry of `J` at the index level: `J(1/q) = J(q)`. -/
theorem costAt_neg_eq (v : MultIndex) : costAt (-v) = costAt v := by
  unfold costAt
  rw [toRat_neg]
  exact (Jcost_symm (toRat_pos v)).symm

/-! ## The state space: free ℝ-module on `MultIndex` -/

/-- The pre-Hilbert space: free `ℝ`-module on `MultIndex`. -/
abbrev StateSpace : Type := MultIndex →₀ ℝ

/-! ## The three operators

We use `Finsupp.lsum` and similar mathlib constructions to define
linear endomorphisms of `StateSpace`.  The "basis vector" `e_v` is
`Finsupp.single v 1`. -/

/-- The diagonal cost operator `D`: maps `e_v` to `J(toRat v) · e_v`.

    Defined as the linear map sending each basis element `e_v` to
    `costAt v • e_v`. -/
def diagOp : StateSpace →ₗ[ℝ] StateSpace :=
  Finsupp.lsum ℝ (fun v => costAt v • Finsupp.lsingle v)

/-- Action of `diagOp` on a basis element: `D(e_v) = costAt v · e_v`. -/
@[simp] theorem diagOp_single (v : MultIndex) (c : ℝ) :
    diagOp (Finsupp.single v c) = Finsupp.single v (costAt v * c) := by
  simp [diagOp, mul_comm]

/-- The prime-shift operator `V_p`: maps `e_v` to `e_{v + δ_p}`,
    i.e., multiplication of the underlying rational by `p`.

    Defined via `Finsupp.lmapDomain` shifting the index by `δ_p`. -/
def shiftOp (p : Nat.Primes) : StateSpace →ₗ[ℝ] StateSpace :=
  Finsupp.lmapDomain ℝ ℝ (fun v => v + Finsupp.single p 1)

/-- Action of `shiftOp p` on a basis element. -/
@[simp] theorem shiftOp_single (p : Nat.Primes) (v : MultIndex) (c : ℝ) :
    shiftOp p (Finsupp.single v c)
      = Finsupp.single (v + Finsupp.single p 1) c := by
  simp [shiftOp, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The inverse prime-shift operator `V_p^{-1}`: maps `e_v` to
    `e_{v - δ_p}` (division of the underlying rational by `p`). -/
def shiftInvOp (p : Nat.Primes) : StateSpace →ₗ[ℝ] StateSpace :=
  Finsupp.lmapDomain ℝ ℝ (fun v => v - Finsupp.single p 1)

@[simp] theorem shiftInvOp_single (p : Nat.Primes) (v : MultIndex) (c : ℝ) :
    shiftInvOp p (Finsupp.single v c)
      = Finsupp.single (v - Finsupp.single p 1) c := by
  simp [shiftInvOp, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- The reciprocal involution operator `U`: maps `e_v` to `e_{-v}`,
    corresponding to the multiplicative inversion `q ↦ 1/q`. -/
def involutionOp : StateSpace →ₗ[ℝ] StateSpace :=
  Finsupp.lmapDomain ℝ ℝ (fun v => -v)

@[simp] theorem involutionOp_single (v : MultIndex) (c : ℝ) :
    involutionOp (Finsupp.single v c) = Finsupp.single (-v) c := by
  simp [involutionOp, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ## Structural theorems -/

/-- The reciprocal involution is involutive: `U ∘ U = id`. -/
theorem involutionOp_involutive : involutionOp ∘ₗ involutionOp = LinearMap.id := by
  ext v
  simp

/-- The reciprocal involution commutes with the diagonal cost operator
    (consequence of `J(1/q) = J(q)`). -/
theorem involutionOp_diagOp_comm :
    involutionOp ∘ₗ diagOp = diagOp ∘ₗ involutionOp := by
  ext v
  simp [costAt_neg_eq]

/-- The reciprocal involution intertwines the prime-shift with its
    inverse: `U ∘ V_p = V_p^{-1} ∘ U`.

    This is the operator-level analog of the zeta functional equation's
    involution `s ↔ 1-s`. -/
theorem involutionOp_shiftOp (p : Nat.Primes) :
    involutionOp ∘ₗ shiftOp p = shiftInvOp p ∘ₗ involutionOp := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply,
             shiftOp_single, involutionOp_single, shiftInvOp_single,
             Finsupp.lsingle_apply]
  congr 1
  abel

/-- Symmetric form of the previous: `U ∘ V_p^{-1} = V_p ∘ U`. -/
theorem involutionOp_shiftInvOp (p : Nat.Primes) :
    involutionOp ∘ₗ shiftInvOp p = shiftOp p ∘ₗ involutionOp := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply,
             shiftInvOp_single, involutionOp_single, shiftOp_single,
             Finsupp.lsingle_apply]
  congr 1
  abel

/-- The shift and inverse-shift compose to the identity (formal unitarity
    of `V_p`). -/
theorem shiftOp_shiftInvOp (p : Nat.Primes) :
    shiftOp p ∘ₗ shiftInvOp p = LinearMap.id := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply,
             shiftInvOp_single, shiftOp_single, Finsupp.lsingle_apply,
             LinearMap.id_apply]
  congr 1
  abel

theorem shiftInvOp_shiftOp (p : Nat.Primes) :
    shiftInvOp p ∘ₗ shiftOp p = LinearMap.id := by
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply,
             shiftOp_single, shiftInvOp_single, Finsupp.lsingle_apply,
             LinearMap.id_apply]
  congr 1
  abel

/-! ## The candidate Hilbert--Pólya operator (algebraic part) -/

/-- The off-diagonal piece for a single prime: `V_p + V_p^{-1}`.
    This is the "hopping" term in the multiplicative direction `p`. -/
def primeHop (p : Nat.Primes) : StateSpace →ₗ[ℝ] StateSpace :=
  shiftOp p + shiftInvOp p

/-- The reciprocal involution maps `V_p + V_p^{-1}` to itself
    (consequence of intertwining shift and inverse shift). -/
theorem involutionOp_primeHop (p : Nat.Primes) :
    involutionOp ∘ₗ primeHop p = primeHop p ∘ₗ involutionOp := by
  unfold primeHop
  rw [LinearMap.comp_add, LinearMap.add_comp]
  rw [involutionOp_shiftOp, involutionOp_shiftInvOp]
  rw [add_comm (shiftInvOp p ∘ₗ involutionOp) (shiftOp p ∘ₗ involutionOp)]

/-- The candidate Hilbert--Pólya operator with weights `λ : Nat.Primes → ℝ`,
    defined on a finite set `S ⊆ Nat.Primes`:
    `T_S(λ) := D + ∑_{p ∈ S} λ p · (V_p + V_p^{-1})`.

    The full operator (sum over all primes) requires choosing a Hilbert space
    closure and analyzing convergence; we work here at the algebraic level
    with a finite truncation. -/
def candidateOp (S : Finset Nat.Primes) (lam : Nat.Primes → ℝ) :
    StateSpace →ₗ[ℝ] StateSpace :=
  diagOp + S.sum (fun p => lam p • primeHop p)

/-- Auxiliary: involution commutes with weighted sum of `primeHop` over a finset.
    Proved by induction on the finset. -/
private theorem involutionOp_sum_primeHop
    (S : Finset Nat.Primes) (lam : Nat.Primes → ℝ) :
    involutionOp ∘ₗ S.sum (fun p => lam p • primeHop p)
      = S.sum (fun p => lam p • primeHop p) ∘ₗ involutionOp := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro p S hp ih
    rw [Finset.sum_insert hp]
    rw [LinearMap.comp_add, LinearMap.add_comp, ih]
    congr 1
    rw [LinearMap.comp_smul, LinearMap.smul_comp]
    congr 1
    exact involutionOp_primeHop p

/-- The candidate operator commutes with the reciprocal involution.
    This is the Hilbert--Pólya-style structural symmetry: any spectrum
    of the (closure of the) operator decomposes into eigenspaces of
    the involution, mirroring `s ↔ 1-s`. -/
theorem involutionOp_candidateOp (S : Finset Nat.Primes) (lam : Nat.Primes → ℝ) :
    involutionOp ∘ₗ candidateOp S lam = candidateOp S lam ∘ₗ involutionOp := by
  unfold candidateOp
  rw [LinearMap.comp_add, LinearMap.add_comp]
  rw [involutionOp_diagOp_comm]
  rw [involutionOp_sum_primeHop]

/-! ## Master certificate -/

/-- Master certificate: the structural properties of the candidate
    Hilbert--Pólya operator that this module establishes. -/
theorem hilbert_polya_candidate_certificate :
    -- (1) Reciprocal symmetry of the cost at the index level.
    (∀ (v : MultIndex), costAt (-v) = costAt v) ∧
    -- (2) The reciprocal involution is involutive.
    (involutionOp ∘ₗ involutionOp = LinearMap.id) ∧
    -- (3) The diagonal cost operator commutes with the involution.
    (involutionOp ∘ₗ diagOp = diagOp ∘ₗ involutionOp) ∧
    -- (4) Each prime shift inverts under the involution.
    (∀ (p : Nat.Primes),
      involutionOp ∘ₗ shiftOp p = shiftInvOp p ∘ₗ involutionOp) ∧
    -- (5) Shifts are formally unitary.
    (∀ (p : Nat.Primes),
      shiftOp p ∘ₗ shiftInvOp p = LinearMap.id) ∧
    -- (6) The full candidate operator commutes with the involution.
    (∀ (S : Finset Nat.Primes) (lam : Nat.Primes → ℝ),
      involutionOp ∘ₗ candidateOp S lam = candidateOp S lam ∘ₗ involutionOp) :=
  ⟨costAt_neg_eq,
   involutionOp_involutive,
   involutionOp_diagOp_comm,
   involutionOp_shiftOp,
   shiftOp_shiftInvOp,
   involutionOp_candidateOp⟩

end

end HilbertPolyaCandidate
end NumberTheory
end IndisputableMonolith
