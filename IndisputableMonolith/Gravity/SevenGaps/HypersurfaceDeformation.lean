import Mathlib

/-!
# Hypersurface deformation: discrete constraint closure on the periodic lattice

QG Seven-Gaps campaign, gap "constraint closure" (Lane 5). This file builds the
first theorem-grade layer of the ADM/Dirac constraint-algebra program for the
discrete gravity effort: a finite-dimensional canonical phase space on a periodic
1D lattice, an honest fderiv-based Poisson bracket, and kernel-checked closure
relations for the discrete constraint generators in the linearized regime.

## Scope (honest)

The `(q, pi)` system here is ONE polarization of the linearized (TT-gauge) field
on a 1D periodic lattice, i.e. a lattice wave field. It is offered as the first
rung of the ADM program, not as full gravity: there is no metric degree of
freedom on this rung, so the continuum structure function `g^{ab}` of the Dirac
algebra is frozen to 1.

## Status ledger

* MODEL: `PhaseSpace`, `pderivQ`/`pderivP`/`bracket` (the bracket is total; on
  observables that are not differentiable at `x` the `fderiv` junk value 0
  enters, so bracket statements about general observables carry explicit
  differentiability hypotheses). `Dgen`, `DgenSym`, `Ham` are definitional
  lattice discretizations of the momentum and Hamiltonian constraints.
* THEOREM (all axiom-clean, no sorry, unconditional unless stated):
  - `bracket_antisymm`, `bracket_self` (no hypotheses);
  - bilinearity `bracket_add_left/right`, `bracket_const_mul_left/right` and
    Leibniz `bracket_mul_left/right`, each with explicit `DifferentiableAt`
    hypotheses (these enter as hypotheses on theorems, never as axioms);
  - canonical relations `bracket_coordQ_coordP`, `bracket_coordQ_coordQ`,
    `bracket_coordP_coordP`;
  - momentum-sector closure `bracket_Dgen_Dgen = 0`,
    `bracket_DgenSym_DgenSym = 0` (the abelian translation sector closes
    sharply: the bracket vanishes identically, it does not merely close up to
    combinations of shift generators);
  - `bracket_Dgen_Ham` (general lapse, forward difference): the TRUE identity,
    derived by hand and then formalized;
  - `bracket_Dgen_Ham_one`: for constant lapse the forward-difference generator
    does NOT commute with `Ham`; the exact closure anomaly is
    `((delta_a d)^2 - (delta_a pi)^2)/2` summed over sites. This CORRECTS the
    naively expected `{H[1], D_a} = 0`: the naive one-sided discretization
    breaks translation closure, and the obstruction is an explicit second-order
    lattice artifact (it is quadratic in the a-step differences of the field
    gradient and momentum, hence vanishes on shift-invariant configurations and
    in the naive continuum limit).
  - `bracket_DgenSym_Ham`: the symmetric-difference momentum generator
    satisfies the EXACT discrete advection (hypersurface-deformation) relation
    `{Dsym_a, H[N]} = (1/2) * sum_j (N(j+a) - N j) * (pi_j pi_{j+a} + d_j d_{j+a})`,
    a point-split smearing of the Hamiltonian density by the lattice derivative
    of the lapse; corollary `bracket_DgenSym_Ham_one = 0` (exact translation
    invariance, constant lapse).
  - `bracket_Ham_Ham`: the discrete hypersurface-deformation relation
    `{H[N], H[M]} = sum_j (N_j M_{j+1} - M_j N_{j+1}) * pi_{j+1} (q_{j+1} - q_j)`:
    two Hamiltonian deformations close on a D-type (momentum) generator whose
    smearing is the discrete Wronskian of the two lapses. In the continuum limit
    `N M' - M N'` smears `pi q'`, which is the Dirac relation
    `{H(N), H(M)} = D(N M' - M N')` with unit structure function on this
    flat scalar rung.
* OPEN:
  - Jacobi for the fderiv bracket. `JacobiOn` names the precise statement; it is
    NOT proved here (for non-C^2 observables it can fail; for polynomial
    observables it is expected but requires second-derivative bookkeeping).
  - The full Dirac algebra recovery in the continuum limit (lattice spacing to
    zero) remains OPEN.
  - The Hojman-Kuchar-Teitelboim (HKT) recovery: the structure
    `HojmanKucharTeitelboimTarget` names, as Prop-valued fields with real
    mathematical content, lattice renderings of the exact HKT hypotheses
    (representation of the hypersurface-deformation algebra by local, covariant
    densities). It is deliberately NOT inhabited: our concrete generators
    realize `mom_mom` exactly but `mom_ham`/`ham_ham` only in point-split form
    (density evaluated at split lattice points), and that gap is precisely the
    discrete-closure frontier. `HKTRigidityStatement` names the rigidity
    conclusion (the deformation algebra forces the Einstein-Hilbert form, here:
    the wave-Hamiltonian form of the density); it is stated, never asserted.

## Design notes

* Sites are `ZMod n` (`n > 0` via `[NeZero n]`), so lattice translation is
  group addition and all reindexing is done by honest sum bijections.
* The bracket is `sum_i (dF/dq_i * dG/dpi_i - dF/dpi_i * dG/dq_i)` with the
  partial derivatives implemented as `fderiv R F x` applied to the basis
  directions `(Pi.single i 1, 0)` and `(0, Pi.single i 1)`. No axiomatized
  bracket, no `: True` fields, no `Nonempty` shells anywhere in this file.
* All generator-closure theorems are unconditional: the generators are
  quadratic polynomials in the coordinates, so every differentiability side
  condition is discharged (`HasFDerivAt` built from `ContinuousLinearMap`
  coordinates via `mul`/`sub`/`add`/`const_mul`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace HypersurfaceDeformation

noncomputable section

open Finset

variable {n : ℕ} [NeZero n]

/-- MODEL. The canonical phase space of the lattice wave field: configuration
`q : ZMod n → ℝ` and conjugate momentum `pi : ZMod n → ℝ` on the periodic
lattice with `n` sites. -/
abbrev PhaseSpace (n : ℕ) : Type := (ZMod n → ℝ) × (ZMod n → ℝ)

/-! ## Coordinate functionals -/

/-- The configuration coordinate `q_i` as a continuous linear functional. -/
def coordQ (i : ZMod n) : PhaseSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (ZMod n → ℝ) (ZMod n → ℝ))

/-- The momentum coordinate `pi_i` as a continuous linear functional. -/
def coordP (i : ZMod n) : PhaseSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ (ZMod n → ℝ) (ZMod n → ℝ))

omit [NeZero n] in
@[simp] lemma coordQ_apply (i : ZMod n) (x : PhaseSpace n) : coordQ i x = x.1 i := rfl

omit [NeZero n] in
@[simp] lemma coordP_apply (i : ZMod n) (x : PhaseSpace n) : coordP i x = x.2 i := rfl

/-! ## Partial derivatives and the Poisson bracket -/

/-- Partial derivative of an observable in the configuration direction `q_i`:
`fderiv` applied to the basis vector `(Pi.single i 1, 0)`. -/
def pderivQ (F : PhaseSpace n → ℝ) (i : ZMod n) (x : PhaseSpace n) : ℝ :=
  fderiv ℝ F x (Pi.single i 1, 0)

/-- Partial derivative of an observable in the momentum direction `pi_i`:
`fderiv` applied to the basis vector `(0, Pi.single i 1)`. -/
def pderivP (F : PhaseSpace n → ℝ) (i : ZMod n) (x : PhaseSpace n) : ℝ :=
  fderiv ℝ F x (0, Pi.single i 1)

/-- MODEL. The Poisson bracket
`{F, G}(x) = sum_i (dF/dq_i * dG/dpi_i - dF/dpi_i * dG/dq_i)`.
Honest but total: for observables not differentiable at `x` the `fderiv` junk
value `0` enters, which is why the general structure theorems below carry
explicit `DifferentiableAt` hypotheses. -/
def bracket (F G : PhaseSpace n → ℝ) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, (pderivQ F i x * pderivP G i x - pderivP F i x * pderivQ G i x)

/-! ## Summation helpers (periodic reindexing and Kronecker collapse) -/

/-- Periodic sums are invariant under lattice translation. -/
lemma sum_shift (a : ZMod n) (f : ZMod n → ℝ) :
    (∑ j : ZMod n, f (j + a)) = ∑ j : ZMod n, f j :=
  Fintype.sum_equiv (Equiv.addRight a) (fun j => f (j + a)) f (fun _ => rfl)

/-- Reindex a periodic sum by the translation `j ↦ j + a`. -/
lemma sum_reindex (a : ZMod n) (f g : ZMod n → ℝ) (h : ∀ j, f (j + a) = g j) :
    (∑ j : ZMod n, f j) = ∑ j : ZMod n, g j := by
  rw [← sum_shift a f]
  exact Finset.sum_congr rfl fun j _ => h j

/-- Kronecker collapse: `sum_i g i * [i = c] = g c`. -/
lemma sum_mul_ite (g : ZMod n → ℝ) (c : ZMod n) :
    (∑ i : ZMod n, g i * (if i = c then (1 : ℝ) else 0)) = g c := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Kronecker collapse with a shifted condition: `sum_i g i * [i + a = c] = g (c - a)`. -/
lemma sum_mul_ite_add (g : ZMod n → ℝ) (a c : ZMod n) :
    (∑ i : ZMod n, g i * (if i + a = c then (1 : ℝ) else 0)) = g (c - a) := by
  rw [Finset.sum_eq_single (c - a)]
  · have h : c - a + a = c := by ring
    simp [h]
  · intro b _ hb
    have hcond : ¬(b + a = c) := by
      intro h
      apply hb
      rw [← h]
      ring
    simp [hcond]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Kronecker collapse with a back-shifted condition: `sum_i g i * [i - a = c] = g (c + a)`. -/
lemma sum_mul_ite_sub (g : ZMod n → ℝ) (a c : ZMod n) :
    (∑ i : ZMod n, g i * (if i - a = c then (1 : ℝ) else 0)) = g (c + a) := by
  rw [Finset.sum_eq_single (c + a)]
  · have h : c + a - a = c := by ring
    simp [h]
  · intro b _ hb
    have hcond : ¬(b - a = c) := by
      intro h
      apply hb
      rw [← h]
      ring
    simp [hcond]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## Structure theorems for the bracket

Antisymmetry is unconditional. Bilinearity and the Leibniz rule hold with
explicit `DifferentiableAt` hypotheses, exactly as far as `fderiv` linearity
gives them. Jacobi is NOT claimed (see `JacobiOn` below, recorded OPEN). -/

/-- THEOREM. Antisymmetry of the bracket (no differentiability needed). -/
theorem bracket_antisymm (F G : PhaseSpace n → ℝ) (x : PhaseSpace n) :
    bracket F G x = - bracket G F x := by
  have h : bracket F G x + bracket G F x = 0 := by
    rw [bracket, bracket, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  linarith

/-- THEOREM. The bracket of an observable with itself vanishes. -/
theorem bracket_self (F : PhaseSpace n → ℝ) (x : PhaseSpace n) :
    bracket F F x = 0 := by
  have h := bracket_antisymm F F x
  linarith

lemma pderivQ_fun_add {F G : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : ZMod n) :
    pderivQ (fun y => F y + G y) i x = pderivQ F i x + pderivQ G i x := by
  simp [pderivQ, fderiv_fun_add hF hG]

lemma pderivP_fun_add {F G : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : ZMod n) :
    pderivP (fun y => F y + G y) i x = pderivP F i x + pderivP G i x := by
  simp [pderivP, fderiv_fun_add hF hG]

lemma pderivQ_const_mul {F : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (c : ℝ) (i : ZMod n) :
    pderivQ (fun y => c * F y) i x = c * pderivQ F i x := by
  simp [pderivQ, (hF.hasFDerivAt.const_mul c).fderiv]

lemma pderivP_const_mul {F : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (c : ℝ) (i : ZMod n) :
    pderivP (fun y => c * F y) i x = c * pderivP F i x := by
  simp [pderivP, (hF.hasFDerivAt.const_mul c).fderiv]

lemma pderivQ_fun_mul {F G : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : ZMod n) :
    pderivQ (fun y => F y * G y) i x = F x * pderivQ G i x + G x * pderivQ F i x := by
  simp [pderivQ, fderiv_fun_mul hF hG]

lemma pderivP_fun_mul {F G : PhaseSpace n → ℝ} {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (i : ZMod n) :
    pderivP (fun y => F y * G y) i x = F x * pderivP G i x + G x * pderivP F i x := by
  simp [pderivP, fderiv_fun_mul hF hG]

/-- THEOREM. Additivity in the first argument (differentiability as explicit
hypotheses, never axioms). -/
theorem bracket_add_left {F G : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ) {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    bracket (fun y => F y + G y) K x = bracket F K x + bracket G K x := by
  simp only [bracket, pderivQ_fun_add hF hG, pderivP_fun_add hF hG]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- THEOREM. Additivity in the second argument. -/
theorem bracket_add_right {F G : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ) {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    bracket K (fun y => F y + G y) x = bracket K F x + bracket K G x := by
  have h1 := bracket_antisymm (n := n) K (fun y => F y + G y) x
  have h2 := bracket_add_left (n := n) K hF hG
  have h3 := bracket_antisymm (n := n) F K x
  have h4 := bracket_antisymm (n := n) G K x
  linarith

/-- THEOREM. Scalar homogeneity in the first argument. -/
theorem bracket_const_mul_left {F : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ)
    {x : PhaseSpace n} (hF : DifferentiableAt ℝ F x) (c : ℝ) :
    bracket (fun y => c * F y) K x = c * bracket F K x := by
  simp only [bracket, pderivQ_const_mul hF c, pderivP_const_mul hF c, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- THEOREM. Scalar homogeneity in the second argument. -/
theorem bracket_const_mul_right {F : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ)
    {x : PhaseSpace n} (hF : DifferentiableAt ℝ F x) (c : ℝ) :
    bracket K (fun y => c * F y) x = c * bracket K F x := by
  have h1 := bracket_antisymm (n := n) K (fun y => c * F y) x
  have h2 := bracket_const_mul_left (n := n) K hF c
  have h3 := bracket_antisymm (n := n) F K x
  linear_combination h1 - h2 - c * h3

/-- THEOREM. Leibniz rule in the first argument (from `fderiv_fun_mul`, with
explicit differentiability hypotheses). -/
theorem bracket_mul_left {F G : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ) {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    bracket (fun y => F y * G y) K x = F x * bracket G K x + G x * bracket F K x := by
  simp only [bracket, pderivQ_fun_mul hF hG, pderivP_fun_mul hF hG, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- THEOREM. Leibniz rule in the second argument. -/
theorem bracket_mul_right {F G : PhaseSpace n → ℝ} (K : PhaseSpace n → ℝ) {x : PhaseSpace n}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    bracket K (fun y => F y * G y) x = F x * bracket K G x + G x * bracket K F x := by
  have h1 := bracket_antisymm (n := n) K (fun y => F y * G y) x
  have h2 := bracket_mul_left (n := n) K hF hG
  have h3 := bracket_antisymm (n := n) G K x
  have h4 := bracket_antisymm (n := n) F K x
  linear_combination h1 - h2 - F x * h3 - G x * h4

/-- OPEN. The Jacobi identity for the fderiv bracket, restricted to a class `S`
of observables. This names the precise statement; it is NOT proved in this
file (and is not expected to hold for observables that are not C^2). Proving it
for the class of quadratic polynomial observables is the natural next rung. -/
def JacobiOn (S : Set (PhaseSpace n → ℝ)) : Prop :=
  ∀ F ∈ S, ∀ G ∈ S, ∀ H ∈ S, ∀ x : PhaseSpace n,
    bracket F (bracket G H) x + bracket G (bracket H F) x + bracket H (bracket F G) x = 0

/-! ## Canonical relations -/

lemma hasFDerivAt_coord_fst (k : ZMod n) (x : PhaseSpace n) :
    HasFDerivAt (fun y : PhaseSpace n => y.1 k) (coordQ k) x :=
  (coordQ k).hasFDerivAt

lemma hasFDerivAt_coord_snd (k : ZMod n) (x : PhaseSpace n) :
    HasFDerivAt (fun y : PhaseSpace n => y.2 k) (coordP k) x :=
  (coordP k).hasFDerivAt

/-- THEOREM. Canonical relation `{q_k, pi_l} = delta_{kl}`. -/
theorem bracket_coordQ_coordP (k l : ZMod n) (x : PhaseSpace n) :
    bracket (fun y : PhaseSpace n => y.1 k) (fun y : PhaseSpace n => y.2 l) x
      = if k = l then (1 : ℝ) else 0 := by
  have hQ : ∀ i : ZMod n, pderivQ (fun y : PhaseSpace n => y.1 k) i x
      = if k = i then (1 : ℝ) else 0 := by
    intro i
    rw [pderivQ, (hasFDerivAt_coord_fst k x).fderiv]
    simp [coordQ, Pi.single_apply]
  have hP0 : ∀ i : ZMod n, pderivP (fun y : PhaseSpace n => y.1 k) i x = 0 := by
    intro i
    rw [pderivP, (hasFDerivAt_coord_fst k x).fderiv]
    simp [coordQ]
  have hP : ∀ i : ZMod n, pderivP (fun y : PhaseSpace n => y.2 l) i x
      = if l = i then (1 : ℝ) else 0 := by
    intro i
    rw [pderivP, (hasFDerivAt_coord_snd l x).fderiv]
    simp [coordP, Pi.single_apply]
  have hQ0 : ∀ i : ZMod n, pderivQ (fun y : PhaseSpace n => y.2 l) i x = 0 := by
    intro i
    rw [pderivQ, (hasFDerivAt_coord_snd l x).fderiv]
    simp [coordP]
  simp only [bracket, hQ, hP, hQ0, hP0, mul_zero, sub_zero]
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hkl]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hk : k = i
    · subst hk
      have : ¬(l = k) := fun h => hkl h.symm
      simp [this]
    · simp [hk]

/-- THEOREM. Canonical relation `{q_k, q_l} = 0`. -/
theorem bracket_coordQ_coordQ (k l : ZMod n) (x : PhaseSpace n) :
    bracket (fun y : PhaseSpace n => y.1 k) (fun y : PhaseSpace n => y.1 l) x = 0 := by
  have hP0k : ∀ i : ZMod n, pderivP (fun y : PhaseSpace n => y.1 k) i x = 0 := by
    intro i
    rw [pderivP, (hasFDerivAt_coord_fst k x).fderiv]
    simp [coordQ]
  have hP0l : ∀ i : ZMod n, pderivP (fun y : PhaseSpace n => y.1 l) i x = 0 := by
    intro i
    rw [pderivP, (hasFDerivAt_coord_fst l x).fderiv]
    simp [coordQ]
  simp only [bracket, hP0k, hP0l, mul_zero, zero_mul, sub_zero]
  exact Finset.sum_eq_zero fun i _ => by ring

/-- THEOREM. Canonical relation `{pi_k, pi_l} = 0`. -/
theorem bracket_coordP_coordP (k l : ZMod n) (x : PhaseSpace n) :
    bracket (fun y : PhaseSpace n => y.2 k) (fun y : PhaseSpace n => y.2 l) x = 0 := by
  have hQ0k : ∀ i : ZMod n, pderivQ (fun y : PhaseSpace n => y.2 k) i x = 0 := by
    intro i
    rw [pderivQ, (hasFDerivAt_coord_snd k x).fderiv]
    simp [coordP]
  have hQ0l : ∀ i : ZMod n, pderivQ (fun y : PhaseSpace n => y.2 l) i x = 0 := by
    intro i
    rw [pderivQ, (hasFDerivAt_coord_snd l x).fderiv]
    simp [coordP]
  simp only [bracket, hQ0k, hQ0l, mul_zero, zero_mul, sub_zero]
  exact Finset.sum_eq_zero fun i _ => by ring

/-! ## The discrete constraint generators

`Dgen a` is the forward-difference (one-sided) discretization of the momentum
constraint smeared by the constant shift vector `a`; `DgenSym a` is the
symmetric-difference discretization; `Ham N` is the smeared quadratic
(linearized) Hamiltonian constraint with lapse `N`. -/

/-- MODEL. Forward-difference momentum (shift) generator
`D_a[q,pi] = sum_i pi_i (q_{i+a} - q_i)`. -/
def Dgen (a : ZMod n) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, x.2 i * (x.1 (i + a) - x.1 i)

/-- MODEL. Symmetric-difference momentum generator
`Dsym_a[q,pi] = (1/2) sum_i pi_i (q_{i+a} - q_{i-a})`. On the periodic lattice
the symmetric difference operator is antisymmetric (discrete integration by
parts with no boundary), and this is exactly what restores the closure of the
momentum-Hamiltonian bracket; see `bracket_DgenSym_Ham`. -/
def DgenSym (a : ZMod n) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, (1 / 2 : ℝ) * (x.2 i * (x.1 (i + a) - x.1 (i - a)))

/-- MODEL. Smeared linearized Hamiltonian constraint
`H[N] = sum_i N_i (pi_i^2 + (q_{i+1} - q_i)^2) / 2`. -/
def Ham (N : ZMod n → ℝ) (x : PhaseSpace n) : ℝ :=
  ∑ i : ZMod n, (N i / 2) * (x.2 i * x.2 i + (x.1 (i + 1) - x.1 i) * (x.1 (i + 1) - x.1 i))

/-- `Ham` agrees with the squared form of the mission statement. -/
lemma Ham_eq_sq (N : ZMod n → ℝ) (x : PhaseSpace n) :
    Ham N x = ∑ i : ZMod n, N i * ((x.2 i) ^ 2 + (x.1 (i + 1) - x.1 i) ^ 2) / 2 :=
  Finset.sum_congr rfl fun i _ => by ring

/-- The symmetric generator is the average of the forward generator and the
reversed one: `Dsym_a = (D_a - D_{-a}) / 2`. -/
lemma DgenSym_eq (a : ZMod n) (x : PhaseSpace n) :
    DgenSym a x = (Dgen a x - Dgen (-a) x) / 2 := by
  rw [DgenSym, Dgen, Dgen, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : i + -a = i - a := by ring
  rw [e]
  ring

/-! ### Frechet derivatives of the generators (all side conditions discharged) -/

/-- The derivative of `Dgen a` at `x`, as an explicit continuous linear map. -/
def DgenD (a : ZMod n) (x : PhaseSpace n) : PhaseSpace n →L[ℝ] ℝ :=
  ∑ i : ZMod n,
    (x.2 i • (coordQ (i + a) - coordQ i) + (x.1 (i + a) - x.1 i) • coordP i)

lemma hasFDerivAt_Dgen (a : ZMod n) (x : PhaseSpace n) :
    HasFDerivAt (Dgen a) (DgenD a x) x := by
  unfold Dgen DgenD
  exact HasFDerivAt.fun_sum fun i _ =>
    (hasFDerivAt_coord_snd i x).mul
      ((hasFDerivAt_coord_fst (i + a) x).sub (hasFDerivAt_coord_fst i x))

/-- THEOREM. `Dgen a` is (unconditionally) differentiable. -/
theorem differentiable_Dgen (a : ZMod n) : Differentiable ℝ (Dgen (n := n) a) :=
  fun x => (hasFDerivAt_Dgen a x).differentiableAt

/-- The derivative of `DgenSym a` at `x`. -/
def DgenSymD (a : ZMod n) (x : PhaseSpace n) : PhaseSpace n →L[ℝ] ℝ :=
  ∑ i : ZMod n,
    (1 / 2 : ℝ) • (x.2 i • (coordQ (i + a) - coordQ (i - a))
      + (x.1 (i + a) - x.1 (i - a)) • coordP i)

lemma hasFDerivAt_DgenSym (a : ZMod n) (x : PhaseSpace n) :
    HasFDerivAt (DgenSym a) (DgenSymD a x) x := by
  unfold DgenSym DgenSymD
  exact HasFDerivAt.fun_sum fun i _ =>
    (((hasFDerivAt_coord_snd i x).mul
      ((hasFDerivAt_coord_fst (i + a) x).sub (hasFDerivAt_coord_fst (i - a) x))).const_mul
        (1 / 2 : ℝ))

/-- THEOREM. `DgenSym a` is (unconditionally) differentiable. -/
theorem differentiable_DgenSym (a : ZMod n) : Differentiable ℝ (DgenSym (n := n) a) :=
  fun x => (hasFDerivAt_DgenSym a x).differentiableAt

/-- The derivative of `Ham N` at `x`. -/
def HamD (N : ZMod n → ℝ) (x : PhaseSpace n) : PhaseSpace n →L[ℝ] ℝ :=
  ∑ i : ZMod n,
    (N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
      + ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
          + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)))

lemma hasFDerivAt_Ham (N : ZMod n → ℝ) (x : PhaseSpace n) :
    HasFDerivAt (Ham N) (HamD N x) x := by
  unfold Ham HamD
  exact HasFDerivAt.fun_sum fun i _ =>
    ((((hasFDerivAt_coord_snd i x).mul (hasFDerivAt_coord_snd i x)).add
      (((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x)).mul
        ((hasFDerivAt_coord_fst (i + 1) x).sub (hasFDerivAt_coord_fst i x)))).const_mul
          (N i / 2))

/-- THEOREM. `Ham N` is (unconditionally) differentiable. -/
theorem differentiable_Ham (N : ZMod n → ℝ) : Differentiable ℝ (Ham (n := n) N) :=
  fun x => (hasFDerivAt_Ham N x).differentiableAt

/-! ### Partial derivatives of the generators (Kronecker collapse) -/

lemma pderivQ_Dgen (a j : ZMod n) (x : PhaseSpace n) :
    pderivQ (Dgen a) j x = x.2 (j - a) - x.2 j := by
  rw [pderivQ, (hasFDerivAt_Dgen a x).fderiv, DgenD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (x.2 i • (coordQ (i + a) - coordQ i) + (x.1 (i + a) - x.1 i) • coordP i)
        ((Pi.single j 1, 0) : PhaseSpace n)
      = x.2 i * (if i + a = j then (1 : ℝ) else 0)
        - x.2 i * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply, mul_sub]
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_sub_distrib,
    sum_mul_ite_add, sum_mul_ite]

lemma pderivP_Dgen (a j : ZMod n) (x : PhaseSpace n) :
    pderivP (Dgen a) j x = x.1 (j + a) - x.1 j := by
  rw [pderivP, (hasFDerivAt_Dgen a x).fderiv, DgenD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (x.2 i • (coordQ (i + a) - coordQ i) + (x.1 (i + a) - x.1 i) • coordP i)
        ((0, Pi.single j 1) : PhaseSpace n)
      = (x.1 (i + a) - x.1 i) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

lemma pderivQ_DgenSym (a j : ZMod n) (x : PhaseSpace n) :
    pderivQ (DgenSym a) j x = (x.2 (j - a) - x.2 (j + a)) / 2 := by
  rw [pderivQ, (hasFDerivAt_DgenSym a x).fderiv, DgenSymD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      ((1 / 2 : ℝ) • (x.2 i • (coordQ (i + a) - coordQ (i - a))
        + (x.1 (i + a) - x.1 (i - a)) • coordP i))
        ((Pi.single j 1, 0) : PhaseSpace n)
      = (x.2 i / 2) * (if i + a = j then (1 : ℝ) else 0)
        - (x.2 i / 2) * (if i - a = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply, mul_sub]
    ring
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_sub_distrib,
    sum_mul_ite_add, sum_mul_ite_sub]
  ring

lemma pderivP_DgenSym (a j : ZMod n) (x : PhaseSpace n) :
    pderivP (DgenSym a) j x = (x.1 (j + a) - x.1 (j - a)) / 2 := by
  rw [pderivP, (hasFDerivAt_DgenSym a x).fderiv, DgenSymD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      ((1 / 2 : ℝ) • (x.2 i • (coordQ (i + a) - coordQ (i - a))
        + (x.1 (i + a) - x.1 (i - a)) • coordP i))
        ((0, Pi.single j 1) : PhaseSpace n)
      = ((x.1 (i + a) - x.1 (i - a)) / 2) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
    ring
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

lemma pderivP_Ham (N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivP (Ham N) j x = N j * x.2 j := by
  rw [pderivP, (hasFDerivAt_Ham N x).fderiv, HamD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
        + ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
            + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i))) :
          PhaseSpace n →L[ℝ] ℝ))
        ((0, Pi.single j 1) : PhaseSpace n)
      = (N i * x.2 i) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, sum_mul_ite]

lemma pderivQ_Ham (N : ZMod n → ℝ) (j : ZMod n) (x : PhaseSpace n) :
    pderivQ (Ham N) j x
      = N (j - 1) * (x.1 j - x.1 (j - 1)) - N j * (x.1 (j + 1) - x.1 j) := by
  rw [pderivQ, (hasFDerivAt_Ham N x).fderiv, HamD, ContinuousLinearMap.sum_apply]
  have step : ∀ i : ZMod n,
      (((N i / 2) • ((x.2 i • coordP i + x.2 i • coordP i)
        + ((x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i)
            + (x.1 (i + 1) - x.1 i) • (coordQ (i + 1) - coordQ i))) :
          PhaseSpace n →L[ℝ] ℝ))
        ((Pi.single j 1, 0) : PhaseSpace n)
      = (N i * (x.1 (i + 1) - x.1 i)) * (if i + 1 = j then (1 : ℝ) else 0)
        - (N i * (x.1 (i + 1) - x.1 i)) * (if i = j then (1 : ℝ) else 0) := by
    intro i
    simp [Pi.single_apply, mul_sub]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun i _ => step i, Finset.sum_sub_distrib,
    sum_mul_ite_add, sum_mul_ite]
  have e : j - 1 + 1 = j := by ring
  rw [e]

/-! ## Closure of the momentum (diffeomorphism) sector

The translation group of the periodic lattice is abelian; the sharp statement
is that the bracket of any two shift generators vanishes identically. -/

/-- THEOREM (momentum sector closes, sharp form). `{D_a, D_b} = 0` for all
lattice displacements `a, b` and every phase-space point. Derived by explicit
computation: after the Kronecker collapse the eight monomial sums cancel in
pairs under the reindexings `j ↦ j + a` and `j ↦ j + b`. -/
theorem bracket_Dgen_Dgen (a b : ZMod n) (x : PhaseSpace n) :
    bracket (Dgen a) (Dgen b) x = 0 := by
  simp only [bracket, pderivQ_Dgen, pderivP_Dgen]
  have h1 : (∑ j : ZMod n, x.2 (j - a) * x.1 (j + b))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a + b)) := by
    refine sum_reindex a (fun k => x.2 (k - a) * x.1 (k + b)) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    have e2 : j + a + b = j + (a + b) := by ring
    simp only [e1, e2]
  have h2 : (∑ j : ZMod n, x.2 (j - a) * x.1 j)
      = ∑ j : ZMod n, x.2 j * x.1 (j + a) := by
    refine sum_reindex a (fun k => x.2 (k - a) * x.1 k) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    simp only [e1]
  have h3 : (∑ j : ZMod n, x.2 (j - b) * x.1 (j + a))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a + b)) := by
    refine sum_reindex b (fun k => x.2 (k - b) * x.1 (k + a)) _ fun j => ?_
    have e1 : j + b - b = j := by ring
    have e2 : j + b + a = j + (a + b) := by ring
    simp only [e1, e2]
  have h4 : (∑ j : ZMod n, x.2 (j - b) * x.1 j)
      = ∑ j : ZMod n, x.2 j * x.1 (j + b) := by
    refine sum_reindex b (fun k => x.2 (k - b) * x.1 k) _ fun j => ?_
    have e1 : j + b - b = j := by ring
    simp only [e1]
  have decomp : (∑ j : ZMod n, ((x.2 (j - a) - x.2 j) * (x.1 (j + b) - x.1 j)
      - (x.1 (j + a) - x.1 j) * (x.2 (j - b) - x.2 j)))
      = ((∑ j : ZMod n, x.2 (j - a) * x.1 (j + b))
          - (∑ j : ZMod n, x.2 (j - a) * x.1 j)
          - (∑ j : ZMod n, x.2 j * x.1 (j + b)))
        - ((∑ j : ZMod n, x.2 (j - b) * x.1 (j + a))
          - (∑ j : ZMod n, x.2 (j - b) * x.1 j)
          - (∑ j : ZMod n, x.2 j * x.1 (j + a))) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decomp, h1, h2, h3, h4]
  ring

/-- THEOREM (momentum sector closes, symmetric discretization).
`{Dsym_a, Dsym_b} = 0`. -/
theorem bracket_DgenSym_DgenSym (a b : ZMod n) (x : PhaseSpace n) :
    bracket (DgenSym a) (DgenSym b) x = 0 := by
  simp only [bracket, pderivQ_DgenSym, pderivP_DgenSym]
  have h1 : (∑ j : ZMod n, x.2 (j - a) * x.1 (j + b))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a + b)) := by
    refine sum_reindex a (fun k => x.2 (k - a) * x.1 (k + b)) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    have e2 : j + a + b = j + (a + b) := by ring
    simp only [e1, e2]
  have h2 : (∑ j : ZMod n, x.2 (j - a) * x.1 (j - b))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a - b)) := by
    refine sum_reindex a (fun k => x.2 (k - a) * x.1 (k - b)) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    have e2 : j + a - b = j + (a - b) := by ring
    simp only [e1, e2]
  have h3 : (∑ j : ZMod n, x.2 (j + a) * x.1 (j + b))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (b - a)) := by
    refine sum_reindex (-a) (fun k => x.2 (k + a) * x.1 (k + b)) _ fun j => ?_
    have e1 : j + -a + a = j := by ring
    have e2 : j + -a + b = j + (b - a) := by ring
    simp only [e1, e2]
  have h4 : (∑ j : ZMod n, x.2 (j + a) * x.1 (j - b))
      = ∑ j : ZMod n, x.2 j * x.1 (j - (a + b)) := by
    refine sum_reindex (-a) (fun k => x.2 (k + a) * x.1 (k - b)) _ fun j => ?_
    have e1 : j + -a + a = j := by ring
    have e2 : j + -a - b = j - (a + b) := by ring
    simp only [e1, e2]
  have h5 : (∑ j : ZMod n, x.2 (j - b) * x.1 (j + a))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a + b)) := by
    refine sum_reindex b (fun k => x.2 (k - b) * x.1 (k + a)) _ fun j => ?_
    have e1 : j + b - b = j := by ring
    have e2 : j + b + a = j + (a + b) := by ring
    simp only [e1, e2]
  have h6 : (∑ j : ZMod n, x.2 (j + b) * x.1 (j + a))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (a - b)) := by
    refine sum_reindex (-b) (fun k => x.2 (k + b) * x.1 (k + a)) _ fun j => ?_
    have e1 : j + -b + b = j := by ring
    have e2 : j + -b + a = j + (a - b) := by ring
    simp only [e1, e2]
  have h7 : (∑ j : ZMod n, x.2 (j - b) * x.1 (j - a))
      = ∑ j : ZMod n, x.2 j * x.1 (j + (b - a)) := by
    refine sum_reindex b (fun k => x.2 (k - b) * x.1 (k - a)) _ fun j => ?_
    have e1 : j + b - b = j := by ring
    have e2 : j + b - a = j + (b - a) := by ring
    simp only [e1, e2]
  have h8 : (∑ j : ZMod n, x.2 (j + b) * x.1 (j - a))
      = ∑ j : ZMod n, x.2 j * x.1 (j - (a + b)) := by
    refine sum_reindex (-b) (fun k => x.2 (k + b) * x.1 (k - a)) _ fun j => ?_
    have e1 : j + -b + b = j := by ring
    have e2 : j + -b - a = j - (a + b) := by ring
    simp only [e1, e2]
  have decomp : (∑ j : ZMod n,
      ((x.2 (j - a) - x.2 (j + a)) / 2 * ((x.1 (j + b) - x.1 (j - b)) / 2)
        - (x.1 (j + a) - x.1 (j - a)) / 2 * ((x.2 (j - b) - x.2 (j + b)) / 2)))
      = (((∑ j : ZMod n, x.2 (j - a) * x.1 (j + b))
          - (∑ j : ZMod n, x.2 (j - a) * x.1 (j - b))
          - (∑ j : ZMod n, x.2 (j + a) * x.1 (j + b))
          + (∑ j : ZMod n, x.2 (j + a) * x.1 (j - b)))
        - ((∑ j : ZMod n, x.2 (j - b) * x.1 (j + a))
          - (∑ j : ZMod n, x.2 (j - b) * x.1 (j - a))
          - (∑ j : ZMod n, x.2 (j + b) * x.1 (j + a))
          + (∑ j : ZMod n, x.2 (j + b) * x.1 (j - a)))) / 4 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decomp, h1, h2, h3, h4, h5, h6, h7, h8]
  ring

/-! ## Momentum-Hamiltonian sector -/

/-- THEOREM (general lapse, forward difference: the TRUE identity).
`{D_a, H[N]} = sum_j N_j (pi_j (pi_{j-a} - pi_j) + d_j (d_j - d_{j+a}))`
where `d_j = q_{j+1} - q_j`. Derived by explicit computation; note it is NOT of
the advected-lapse form: the one-sided difference generator does not represent
lattice translations exactly. -/
theorem bracket_Dgen_Ham (a : ZMod n) (N : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (Dgen a) (Ham N) x
      = ∑ j : ZMod n, N j * (x.2 j * (x.2 (j - a) - x.2 j)
          + (x.1 (j + 1) - x.1 j)
            * ((x.1 (j + 1) - x.1 j) - (x.1 (j + a + 1) - x.1 (j + a)))) := by
  simp only [bracket, pderivQ_Dgen, pderivP_Dgen, pderivQ_Ham, pderivP_Ham]
  have decomp1 : (∑ j : ZMod n, ((x.2 (j - a) - x.2 j) * (N j * x.2 j)
      - (x.1 (j + a) - x.1 j)
        * (N (j - 1) * (x.1 j - x.1 (j - 1)) - N j * (x.1 (j + 1) - x.1 j))))
      = (∑ j : ZMod n, ((x.2 (j - a) - x.2 j) * (N j * x.2 j)
          + (x.1 (j + a) - x.1 j) * (N j * (x.1 (j + 1) - x.1 j))))
        - (∑ j : ZMod n, (x.1 (j + a) - x.1 j) * (N (j - 1) * (x.1 j - x.1 (j - 1)))) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decomp1]
  have hshift : (∑ j : ZMod n, (x.1 (j + a) - x.1 j) * (N (j - 1) * (x.1 j - x.1 (j - 1))))
      = ∑ j : ZMod n, (x.1 (j + a + 1) - x.1 (j + 1)) * (N j * (x.1 (j + 1) - x.1 j)) := by
    refine sum_reindex 1
      (fun k => (x.1 (k + a) - x.1 k) * (N (k - 1) * (x.1 k - x.1 (k - 1)))) _ fun j => ?_
    have e1 : j + 1 - 1 = j := by ring
    have e2 : j + 1 + a = j + a + 1 := by ring
    simp only [e1, e2]
  rw [hshift, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- THEOREM (constant lapse: the exact closure ANOMALY of the forward
difference). `{D_a, H[1]} = (1/2) sum_j ((d_{j+a} - d_j)^2 - (pi_{j+a} - pi_j)^2)`.
This is generically nonzero: the naive one-sided discretization of the momentum
constraint does not commute with the constant-lapse Hamiltonian. The obstruction
is an explicit lattice artifact, quadratic in the `a`-step differences of the
field gradient `d` and the momentum `pi`; it vanishes identically on
shift-invariant configurations. This theorem corrects the naive expectation
`{H[1], D_a} = 0` (which DOES hold for the symmetric generator, see
`bracket_DgenSym_Ham_one`). -/
theorem bracket_Dgen_Ham_one (a : ZMod n) (x : PhaseSpace n) :
    bracket (Dgen a) (Ham (fun _ => 1)) x
      = (∑ j : ZMod n,
          (((x.1 (j + a + 1) - x.1 (j + a)) - (x.1 (j + 1) - x.1 j)) ^ 2
            - (x.2 (j + a) - x.2 j) ^ 2)) / 2 := by
  simp only [bracket_Dgen_Ham, one_mul]
  have hP1 : (∑ j : ZMod n, x.2 j * x.2 (j - a))
      = ∑ j : ZMod n, x.2 (j + a) * x.2 j := by
    refine sum_reindex a (fun k => x.2 k * x.2 (k - a)) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    simp only [e1]
  have hP2 : (∑ j : ZMod n, x.2 j * x.2 j)
      = ∑ j : ZMod n, x.2 (j + a) * x.2 (j + a) :=
    sum_reindex a (fun k => x.2 k * x.2 k) _ fun j => rfl
  have hQ1 : (∑ j : ZMod n, (x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))
      = ∑ j : ZMod n, (x.1 (j + a + 1) - x.1 (j + a)) * (x.1 (j + a + 1) - x.1 (j + a)) :=
    sum_reindex a (fun k => (x.1 (k + 1) - x.1 k) * (x.1 (k + 1) - x.1 k)) _ fun j => rfl
  have decompL : (∑ j : ZMod n, (x.2 j * (x.2 (j - a) - x.2 j)
      + (x.1 (j + 1) - x.1 j)
        * ((x.1 (j + 1) - x.1 j) - (x.1 (j + a + 1) - x.1 (j + a)))))
      = ((∑ j : ZMod n, x.2 j * x.2 (j - a)) - (∑ j : ZMod n, x.2 j * x.2 j))
        + ((∑ j : ZMod n, (x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j))
          - (∑ j : ZMod n,
              (x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a)))) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have decompR : (∑ j : ZMod n,
      (((x.1 (j + a + 1) - x.1 (j + a)) - (x.1 (j + 1) - x.1 j)) ^ 2
        - (x.2 (j + a) - x.2 j) ^ 2))
      = ((∑ j : ZMod n, (x.1 (j + a + 1) - x.1 (j + a)) * (x.1 (j + a + 1) - x.1 (j + a)))
          - 2 * (∑ j : ZMod n, (x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a)))
          + (∑ j : ZMod n, (x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)))
        - ((∑ j : ZMod n, x.2 (j + a) * x.2 (j + a))
          - 2 * (∑ j : ZMod n, x.2 (j + a) * x.2 j)
          + (∑ j : ZMod n, x.2 j * x.2 j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decompL, decompR, ← hQ1, ← hP2, ← hP1]
  ring

/-- THEOREM (exact discrete advection / hypersurface deformation, momentum vs
Hamiltonian). For the symmetric-difference generator the bracket with the
smeared Hamiltonian is EXACTLY the point-split Hamiltonian density smeared by
the discrete derivative of the lapse:
`{Dsym_a, H[N]} = (1/2) sum_j (N_{j+a} - N_j) (pi_j pi_{j+a} + d_j d_{j+a})`.
For constant lapse the right side vanishes identically
(`bracket_DgenSym_Ham_one`): the symmetric discretization restores exact
translation closure. In the continuum limit `N_{j+a} - N_j` tends to `a N'` and
the point-split density tends to `pi^2 + (q')^2`, recovering the Dirac relation
`{D(xi), H(N)} = H(xi N')` on this rung. -/
theorem bracket_DgenSym_Ham (a : ZMod n) (N : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (DgenSym a) (Ham N) x
      = (∑ j : ZMod n, (N (j + a) - N j)
          * (x.2 j * x.2 (j + a)
            + (x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a)))) / 2 := by
  simp only [bracket, pderivQ_DgenSym, pderivP_DgenSym, pderivQ_Ham, pderivP_Ham]
  -- Stage 1: split off the `N (j-1)` piece and reindex it by one lattice step.
  have decompL : (∑ j : ZMod n, ((x.2 (j - a) - x.2 (j + a)) / 2 * (N j * x.2 j)
      - (x.1 (j + a) - x.1 (j - a)) / 2
        * (N (j - 1) * (x.1 j - x.1 (j - 1)) - N j * (x.1 (j + 1) - x.1 j))))
      = ((∑ j : ZMod n, N j * (x.2 j * x.2 (j - a)))
          - (∑ j : ZMod n, N j * (x.2 j * x.2 (j + a)))
          + (∑ j : ZMod n,
              (x.1 (j + a) - x.1 (j - a)) * (N j * (x.1 (j + 1) - x.1 j)))
          - (∑ j : ZMod n,
              (x.1 (j + a) - x.1 (j - a)) * (N (j - 1) * (x.1 j - x.1 (j - 1))))) / 2 := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decompL]
  have hshift : (∑ j : ZMod n,
      (x.1 (j + a) - x.1 (j - a)) * (N (j - 1) * (x.1 j - x.1 (j - 1))))
      = ∑ j : ZMod n,
        (x.1 (j + a + 1) - x.1 (j - a + 1)) * (N j * (x.1 (j + 1) - x.1 j)) := by
    refine sum_reindex 1
      (fun k => (x.1 (k + a) - x.1 (k - a)) * (N (k - 1) * (x.1 k - x.1 (k - 1)))) _
      fun j => ?_
    have e1 : j + 1 - 1 = j := by ring
    have e2 : j + 1 + a = j + a + 1 := by ring
    have e3 : j + 1 - a = j - a + 1 := by ring
    simp only [e1, e2, e3]
  rw [hshift]
  -- Stage 2: reindex the two back-shifted sums to canonical forward form.
  have hpi : (∑ j : ZMod n, N j * (x.2 j * x.2 (j - a)))
      = ∑ j : ZMod n, N (j + a) * (x.2 j * x.2 (j + a)) := by
    refine sum_reindex a (fun k => N k * (x.2 k * x.2 (k - a))) _ fun j => ?_
    have e1 : j + a - a = j := by ring
    simp only [e1]
    ring
  rw [hpi]
  -- Stage 3: convert the two q-sums into point-split gradient sums.
  have decompQ : (∑ j : ZMod n,
      (x.1 (j + a) - x.1 (j - a)) * (N j * (x.1 (j + 1) - x.1 j)))
      - (∑ j : ZMod n,
          (x.1 (j + a + 1) - x.1 (j - a + 1)) * (N j * (x.1 (j + 1) - x.1 j)))
      = (∑ j : ZMod n,
          N j * ((x.1 (j + 1) - x.1 j) * (x.1 (j - a + 1) - x.1 (j - a))))
        - (∑ j : ZMod n,
            N j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a)))) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgrad : (∑ j : ZMod n,
      N j * ((x.1 (j + 1) - x.1 j) * (x.1 (j - a + 1) - x.1 (j - a))))
      = ∑ j : ZMod n,
        N (j + a) * ((x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a))) := by
    refine sum_reindex a
      (fun k => N k * ((x.1 (k + 1) - x.1 k) * (x.1 (k - a + 1) - x.1 (k - a)))) _
      fun j => ?_
    have e1 : j + a - a = j := by ring
    simp only [e1]
    ring
  have decompR : (∑ j : ZMod n, (N (j + a) - N j)
      * (x.2 j * x.2 (j + a)
        + (x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a))))
      = ((∑ j : ZMod n, N (j + a) * (x.2 j * x.2 (j + a)))
          - (∑ j : ZMod n, N j * (x.2 j * x.2 (j + a))))
        + ((∑ j : ZMod n,
            N (j + a) * ((x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a))))
          - (∑ j : ZMod n,
              N j * ((x.1 (j + 1) - x.1 j) * (x.1 (j + a + 1) - x.1 (j + a))))) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [decompR]
  have key := decompQ
  rw [hgrad] at key
  linarith [key]

/-- THEOREM. Constant lapse: the symmetric-difference momentum generator
commutes exactly with the Hamiltonian, `{Dsym_a, H[1]} = 0` (exact discrete
translation invariance). -/
theorem bracket_DgenSym_Ham_one (a : ZMod n) (x : PhaseSpace n) :
    bracket (DgenSym a) (Ham (fun _ => 1)) x = 0 := by
  rw [bracket_DgenSym_Ham]
  simp

/-- THEOREM. `{H[1], Dsym_a} = 0` (the flipped orientation, via antisymmetry). -/
theorem bracket_Ham_one_DgenSym (a : ZMod n) (x : PhaseSpace n) :
    bracket (Ham (fun _ => 1)) (DgenSym a) x = 0 := by
  rw [bracket_antisymm, bracket_DgenSym_Ham_one, neg_zero]

/-! ## Hamiltonian-Hamiltonian sector: the hypersurface-deformation relation -/

/-- THEOREM (discrete hypersurface-deformation relation).
`{H[N], H[M]} = sum_j (N_j M_{j+1} - M_j N_{j+1}) * pi_{j+1} (q_{j+1} - q_j)`.
The bracket of two Hamiltonian deformations is a D-type (momentum) generator:
a point-split momentum density `pi_{j+1} (q_{j+1} - q_j)` smeared by the
discrete Wronskian `N_j M_{j+1} - M_j N_{j+1}` of the two lapses. In the
continuum limit the Wronskian tends to `(N M' - M N') dx` and the density to
`pi q'`, which is the Dirac algebra relation `{H(N), H(M)} = D(N M' - M N')`;
the structure function (the inverse spatial metric in full gravity) is frozen
to 1 on this flat scalar rung. Antisymmetric in `N, M` by inspection, and it
vanishes identically for `N = M`. -/
theorem bracket_Ham_Ham (N M : ZMod n → ℝ) (x : PhaseSpace n) :
    bracket (Ham N) (Ham M) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1))
          * (x.2 (j + 1) * (x.1 (j + 1) - x.1 j)) := by
  simp only [bracket, pderivQ_Ham, pderivP_Ham]
  have step1 : (∑ j : ZMod n,
      ((N (j - 1) * (x.1 j - x.1 (j - 1)) - N j * (x.1 (j + 1) - x.1 j)) * (M j * x.2 j)
        - N j * x.2 j
          * (M (j - 1) * (x.1 j - x.1 (j - 1)) - M j * (x.1 (j + 1) - x.1 j))))
      = ∑ j : ZMod n,
          (N (j - 1) * M j - M (j - 1) * N j) * (x.2 j * (x.1 j - x.1 (j - 1))) :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [step1]
  refine sum_reindex 1
    (fun k => (N (k - 1) * M k - M (k - 1) * N k) * (x.2 k * (x.1 k - x.1 (k - 1)))) _
    fun j => ?_
  have e1 : j + 1 - 1 = j := by ring
  simp only [e1]

end

/-! ## The Hojman-Kuchar-Teitelboim target (honesty layer)

The HKT theorem (Hojman, Kuchar, Teitelboim 1976) says: a representation of the
hypersurface-deformation (Dirac) algebra on a metric phase space, by local
covariant constraint densities with the metric-dependent structure function in
the `{H, H}` bracket, forces the Hamiltonian constraint to have the
Einstein-Hilbert (ADM) form up to Newton and cosmological constants. The
structure below names lattice renderings of the exact hypotheses as Prop-valued
fields with real mathematical content. It is deliberately NOT inhabited in this
file: the concrete generators above realize `mom_mom` exactly but satisfy the
`mom_ham` and `ham_ham` relations only in point-split form (the density
evaluated at split lattice points, see `bracket_DgenSym_Ham` and
`bracket_Ham_Ham`), and closing that gap, together with the continuum limit and
the rigidity implication `HKTRigidityStatement`, remains OPEN. -/

/-- OPEN TARGET (deliberately uninhabited). The hypotheses of the
Hojman-Kuchar-Teitelboim theorem, rendered on the periodic lattice: local,
translation-covariant Hamiltonian and momentum densities whose smeared
generators represent the hypersurface-deformation algebra: abelian momentum
sector (`mom_mom`), lapse advection (`mom_ham`), and the `{H, H}` relation
closing on the momentum density with the Wronskian smearing (`ham_ham`; the
structure function is 1 on this flat scalar rung, in full gravity it is the
inverse spatial metric). Every field is a real mathematical statement; none is
`True` and no instance is provided anywhere in this file. -/
structure HojmanKucharTeitelboimTarget (n : ℕ) [NeZero n] where
  /-- The local Hamiltonian-constraint density `h_j[q, pi]`. -/
  hamDensity : PhaseSpace n → ZMod n → ℝ
  /-- The local momentum-constraint density `p_j[q, pi]`. -/
  momDensity : PhaseSpace n → ZMod n → ℝ
  /-- Smeared Hamiltonian generators are differentiable observables. -/
  ham_differentiable : ∀ N : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, N j * hamDensity x j)
  /-- Smeared momentum generators are differentiable observables. -/
  mom_differentiable : ∀ w : ZMod n → ℝ,
    Differentiable ℝ (fun x : PhaseSpace n => ∑ j : ZMod n, w j * momDensity x j)
  /-- Locality: the Hamiltonian density at site `j` depends only on the field
  in the elementary cell `{j, j+1}` and the momentum at `j`. -/
  ham_local : ∀ (x y : PhaseSpace n) (j : ZMod n),
    x.1 j = y.1 j → x.1 (j + 1) = y.1 (j + 1) → x.2 j = y.2 j →
      hamDensity x j = hamDensity y j
  /-- Translation covariance of the Hamiltonian density. -/
  ham_covariant : ∀ (x : PhaseSpace n) (a j : ZMod n),
    hamDensity (fun i => x.1 (i + a), fun i => x.2 (i + a)) j = hamDensity x (j + a)
  /-- Dirac relation 1: the smeared momentum sector is abelian. -/
  mom_mom : ∀ (v w : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, v j * momDensity y j)
      (fun y => ∑ j : ZMod n, w j * momDensity y j) x = 0
  /-- Dirac relation 2: the momentum generator advects the lapse,
  `{D[w], H[N]} = H[w * (discrete derivative of N)]`. -/
  mom_ham : ∀ (w N : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, w j * momDensity y j)
      (fun y => ∑ j : ZMod n, N j * hamDensity y j) x
      = ∑ j : ZMod n, (w j * (N (j + 1) - N j)) * hamDensity x j
  /-- Dirac relation 3 (hypersurface deformation): two Hamiltonian deformations
  close on the momentum density smeared by the discrete Wronskian of the
  lapses. -/
  ham_ham : ∀ (N M : ZMod n → ℝ) (x : PhaseSpace n),
    bracket (fun y => ∑ j : ZMod n, N j * hamDensity y j)
      (fun y => ∑ j : ZMod n, M j * hamDensity y j) x
      = ∑ j : ZMod n, (N j * M (j + 1) - M j * N (j + 1)) * momDensity x j

/-- OPEN. The HKT rigidity statement on this rung: any representation of the
hypersurface-deformation algebra in the sense of `HojmanKucharTeitelboimTarget`
has a Hamiltonian density of the canonical (wave / Einstein-Hilbert-form)
shape, kinetic plus gradient-squared plus a vacuum constant. This Prop is
DEFINED here so the target is precise; it is neither proved nor assumed
anywhere in this file, and no axiom about it is introduced. -/
def HKTRigidityStatement (n : ℕ) [NeZero n] : Prop :=
  ∀ T : HojmanKucharTeitelboimTarget n,
    ∃ cKin cGrad cVac : ℝ, ∀ (x : PhaseSpace n) (j : ZMod n),
      T.hamDensity x j
        = cKin * (x.2 j * x.2 j)
          + cGrad * ((x.1 (j + 1) - x.1 j) * (x.1 (j + 1) - x.1 j)) + cVac

end HypersurfaceDeformation
end SevenGaps
end Gravity
end IndisputableMonolith
