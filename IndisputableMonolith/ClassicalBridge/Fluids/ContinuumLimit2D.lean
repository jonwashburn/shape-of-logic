import Mathlib
import IndisputableMonolith.ClassicalBridge.Fluids.Galerkin2D
import IndisputableMonolith.ClassicalBridge.Fluids.CPM2D

namespace IndisputableMonolith.ClassicalBridge.Fluids

open Real
open Filter
open Topology
open scoped InnerProductSpace

/-!
# ContinuumLimit2D (Milestone M5)

This file defines a *Lean-checkable pipeline shape* for passing from a family of finite-dimensional
2D Galerkin approximations to a “continuum” limit object.

At this milestone we stay honest about what is and is not formalized:
- we define the relevant objects (an infinite Fourier coefficient state),
- we define the canonical embedding of truncated coefficients into the full Fourier state, and
- we package the analytic compactness/identification steps as explicit hypotheses (no `axiom`, no `sorry`).

The point is to make the dependency graph explicit so that later milestones can progressively
replace hypotheses with proofs.
-/

namespace ContinuumLimit2D

/-!
## Continuum Fourier state on 𝕋²

We model a 2D torus velocity field via its Fourier coefficients:
for each `k : Mode2 = ℤ×ℤ`, a coefficient `VelCoeff = EuclideanSpace ℝ (Fin 2)`.
-/

/-- Full (infinite) Fourier coefficient state for a 2D velocity field on 𝕋². -/
abbrev FourierState2D : Type := Mode2 → VelCoeff

/-!
## Embedding: GalerkinState N → FourierState2D

We extend a truncated state by zero outside the truncation window.
-/

/-- Read a single component coefficient at mode `k` (zero if `k ∉ modes N`). -/
noncomputable def coeffAt {N : ℕ} (u : GalerkinState N) (k : Mode2) (j : Fin 2) : ℝ :=
  if hk : k ∈ modes N then
    -- `k` as an element of the finite index type `(modes N)`
    let k' : (modes N) := ⟨k, hk⟩
    u (k', j)
  else
    0

/-- Extend a truncated Galerkin state by zero to a full Fourier coefficient state. -/
noncomputable def extendByZero {N : ℕ} (u : GalerkinState N) : FourierState2D :=
  fun k =>
    -- Build a 2-vector coefficient from its two components.
    !₂[coeffAt u k ⟨0, by decide⟩, coeffAt u k ⟨1, by decide⟩]

/-!
## Linearity of the zero-extension embedding

We will eventually want to pass (linear) identities from Galerkin trajectories to limits.
For that, it is useful to record that `extendByZero` is a linear map.
-/

lemma coeffAt_add {N : ℕ} (u v : GalerkinState N) (k : Mode2) (j : Fin 2) :
    coeffAt (u + v) k j = coeffAt u k j + coeffAt v k j := by
  classical
  by_cases hk : k ∈ modes N
  · simp [coeffAt, hk]
  · simp [coeffAt, hk]

lemma coeffAt_smul {N : ℕ} (c : ℝ) (u : GalerkinState N) (k : Mode2) (j : Fin 2) :
    coeffAt (c • u) k j = c * coeffAt u k j := by
  classical
  by_cases hk : k ∈ modes N
  · simp [coeffAt, hk]
  · simp [coeffAt, hk]

lemma extendByZero_add {N : ℕ} (u v : GalerkinState N) :
    extendByZero (u + v) = extendByZero u + extendByZero v := by
  classical
  funext k
  ext j
  fin_cases j <;> simp [extendByZero, coeffAt_add]

lemma extendByZero_smul {N : ℕ} (c : ℝ) (u : GalerkinState N) :
    extendByZero (c • u) = c • (extendByZero u) := by
  classical
  funext k
  ext j
  fin_cases j <;> simp [extendByZero, coeffAt_smul]

lemma extendByZero_neg {N : ℕ} (u : GalerkinState N) :
    extendByZero (-u) = -extendByZero u := by
  classical
  -- `-u = (-1) • u` and `extendByZero` is linear.
  simpa [neg_one_smul] using (extendByZero_smul (N := N) (-1) u)

/-- `extendByZero` packaged as a linear map. -/
noncomputable def extendByZeroLinear (N : ℕ) : GalerkinState N →ₗ[ℝ] FourierState2D :=
  { toFun := extendByZero
    map_add' := extendByZero_add (N := N)
    map_smul' := by
      intro c u
      -- `simp` expects `c • x`; our lemma is stated in that form.
      simpa using (extendByZero_smul (N := N) c u) }

/-- `extendByZero` as a *continuous* linear map.

This is available because `GalerkinState N` is finite-dimensional, hence every linear map out of it
is continuous. -/
noncomputable def extendByZeroCLM (N : ℕ) : GalerkinState N →L[ℝ] FourierState2D :=
  LinearMap.toContinuousLinearMap (extendByZeroLinear N)

/-!
## Divergence-free structure (Fourier side) and limit stability

A structural property we can pass to the limit using only modewise convergence is a closed,
linear constraint such as “divergence-free in Fourier variables”:

`k₁ * û₁(t,k) + k₂ * û₂(t,k) = 0` for every mode `k`.
-/

/-- Real Fourier-side divergence constraint for a single mode. -/
noncomputable def divConstraint (k : Mode2) (v : VelCoeff) : ℝ :=
  (k.1 : ℝ) * v (0 : Fin 2) + (k.2 : ℝ) * v (1 : Fin 2)

/-- Fourier-side divergence-free predicate (modewise, at a fixed time). -/
def IsDivergenceFree (u : FourierState2D) : Prop :=
  ∀ k : Mode2, divConstraint k (u k) = 0

/-- Divergence-free predicate for a time-dependent Fourier trajectory. -/
def IsDivergenceFreeTraj (u : ℝ → FourierState2D) : Prop :=
  ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((u t) k) = 0

lemma divConstraint_continuous (k : Mode2) : Continuous fun v : VelCoeff => divConstraint k v := by
  have h0 : Continuous fun v : VelCoeff => v (0 : Fin 2) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2))
  have h1 : Continuous fun v : VelCoeff => v (1 : Fin 2) := by
    simpa using
      (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2))
  simpa [divConstraint] using ((continuous_const.mul h0).add (continuous_const.mul h1))

/-!
## Linear Stokes/heat mild form (Fourier side) and limit stability

As a next step toward a real PDE statement, we can talk about the *linear* (viscous) dynamics.
On the Fourier side, the Stokes/heat semigroup acts diagonally:

`û(t,k) = exp(-ν |k|^2 t) • û(0,k)`.

This is still not Navier–Stokes, but it is a concrete PDE-like identity that can be passed to the
limit using only modewise convergence (no compactness beyond that).
-/

/-- Fourier-side heat/Stokes factor `e^{-ν|k|^2 t}`. -/
noncomputable def heatFactor (ν : ℝ) (t : ℝ) (k : Mode2) : ℝ :=
  Real.exp (-ν * kSq k * t)

/-- Mild Stokes/heat solution in Fourier coefficients (modewise, for `t ≥ 0`). -/
def IsStokesMildTraj (ν : ℝ) (u : ℝ → FourierState2D) : Prop :=
  ∀ t ≥ 0, ∀ k : Mode2, (u t) k = (heatFactor ν t k) • (u 0) k

/-- Differential (within `t ≥ 0`) Stokes/heat equation in Fourier coefficients (modewise).

This is a slightly more “PDE-like” statement than the mild form: for each fixed mode `k`,
the coefficient trajectory satisfies

`d/dt u(t,k) = -(ν |k|^2) • u(t,k)`

as a derivative **within** the half-line `[0,∞)`. -/
def IsStokesODETraj (ν : ℝ) (u : ℝ → FourierState2D) : Prop :=
  ∀ t ≥ 0, ∀ k : Mode2,
    HasDerivWithinAt (fun s : ℝ => (u s) k) (-(ν * kSq k) • (u t) k) (Set.Ici (0 : ℝ)) t

/-!
## First nonlinear (Duhamel-style) identification: heat evolution + remainder

To start introducing the nonlinear Navier–Stokes term without committing to the full analytic
infrastructure (time integrals, dominated convergence, etc.), we use a *Duhamel-like remainder*
term `D(t,k)`:

`u(t,k) = heatFactor(ν,t,k) • u(0,k) + D(t,k)`.

In a future milestone, `D` will be instantiated as the time-integrated nonlinear forcing.
For now, this already gives a useful “nonlinear-shaped” identity that can be passed to the limit
under modewise convergence, provided the remainders also converge modewise.
-/

/-- Duhamel-style (nonlinear) remainder form: `u = heatFactor • u0 + D` (modewise, for `t ≥ 0`). -/
def IsNSDuhamelTraj (ν : ℝ) (D : ℝ → FourierState2D) (u : ℝ → FourierState2D) : Prop :=
  ∀ t ≥ 0, ∀ k : Mode2, (u t) k = (heatFactor ν t k) • (u 0) k + (D t) k

namespace IsStokesMildTraj

/-- Mild Stokes/heat identity implies the corresponding differential equation (within `t ≥ 0`). -/
theorem stokesODE {ν : ℝ} {u : ℝ → FourierState2D} (h : IsStokesMildTraj ν u) :
    IsStokesODETraj ν u := by
  intro t ht k
  -- Let `a = u(0,k)` so the mild formula reads `u(s,k) = exp(-ν|k|^2 s) • a` for `s ≥ 0`.
  let a : VelCoeff := (u 0) k

  -- Derivative of the scalar heat factor.
  have hlin : HasDerivAt (fun s : ℝ => (-ν * kSq k) * s) (-ν * kSq k) t := by
    simpa [mul_assoc] using (hasDerivAt_id t).const_mul (-ν * kSq k)
  have hscalar :
      HasDerivAt (fun s : ℝ => heatFactor ν s k)
        (heatFactor ν t k * (-ν * kSq k)) t := by
    -- `d/ds exp(g(s)) = exp(g(s)) * g'(s)` with `g(s) = (-ν|k|^2) * s`.
    have hexp :
        HasDerivAt (fun s : ℝ => Real.exp ((-ν * kSq k) * s))
          (Real.exp ((-ν * kSq k) * t) * (-ν * kSq k)) t :=
      (Real.hasDerivAt_exp ((-ν * kSq k) * t)).comp t hlin
    simpa [heatFactor, mul_assoc] using hexp
  have hscalarW :
      HasDerivWithinAt (fun s : ℝ => heatFactor ν s k)
        (heatFactor ν t k * (-ν * kSq k)) (Set.Ici (0 : ℝ)) t :=
    hscalar.hasDerivWithinAt

  -- Differentiate `s ↦ heatFactor ν s k • a` within `[0,∞)`.
  have hform :
      HasDerivWithinAt (fun s : ℝ => (heatFactor ν s k) • a)
        ((heatFactor ν t k * (-ν * kSq k)) • a) (Set.Ici (0 : ℝ)) t :=
    hscalarW.smul_const a

  -- Replace the formula by `u` using the mild identity on the domain `[0,∞)`.
  have huEq : ∀ s ∈ Set.Ici (0 : ℝ), (fun s : ℝ => (u s) k) s = (fun s : ℝ => (heatFactor ν s k) • a) s := by
    intro s hs
    -- `hs : 0 ≤ s`
    simpa [a] using (h s hs k)
  have huEq_t : (fun s : ℝ => (u s) k) t = (fun s : ℝ => (heatFactor ν s k) • a) t := by
    simpa [a] using (h t ht k)

  have huDeriv :
      HasDerivWithinAt (fun s : ℝ => (u s) k) ((heatFactor ν t k * (-ν * kSq k)) • a)
        (Set.Ici (0 : ℝ)) t :=
    hform.congr huEq huEq_t

  -- Simplify the derivative into `-(ν|k|^2) • u(t,k)`.
  have hsimp :
      ((heatFactor ν t k * (-ν * kSq k)) • a) = (-(ν * kSq k)) • ((u t) k) := by
    -- Use commutativity of real multiplication to flip the order, then `mul_smul`.
    have hut : (u t) k = (heatFactor ν t k) • a := by
      simpa [a] using (h t ht k)
    -- Rewrite to match `mul_smul` and then substitute `hut`.
    calc
      (heatFactor ν t k * (-ν * kSq k)) • a
          = ((-ν * kSq k) * heatFactor ν t k) • a := by
              simp [mul_comm, mul_assoc]
      _ = (-ν * kSq k) • ((heatFactor ν t k) • a) := by
              simp [mul_smul]
      _ = (-(ν * kSq k)) • ((heatFactor ν t k) • a) := by ring_nf
      _ = (-(ν * kSq k)) • ((u t) k) := by simp [hut]

  -- `simp` may rewrite `heatFactor * (-ν*kSq)` as `-(heatFactor * (ν*kSq))`, so we also register
  -- a simp-friendly variant with the outer negation.
  have hsimp_neg :
      -((heatFactor ν t k * (ν * kSq k)) • a) = (-(ν * kSq k)) • ((u t) k) := by
    -- Move the `-` inside as `(-1) • _` and simplify using `hsimp`.
    have : (heatFactor ν t k * (-ν * kSq k)) • a = -((heatFactor ν t k * (ν * kSq k)) • a) := by
      -- scalar arithmetic in `ℝ` + `(-r) • a = -(r • a)`
      calc
        (heatFactor ν t k * (-ν * kSq k)) • a
            = (-(heatFactor ν t k * (ν * kSq k))) • a := by ring_nf
        _ = -((heatFactor ν t k * (ν * kSq k)) • a) := by
            simp [neg_smul]
    -- Now rewrite and finish.
    simpa [this] using hsimp

  simpa [IsStokesODETraj, hsimp_neg] using huDeriv

end IsStokesMildTraj

/-!
## Galerkin → Fourier coefficient dynamics (modewise ODE, with nonlinearity)

This is the first genuinely “Navier–Stokes shaped” bridge lemma: if a Galerkin trajectory satisfies
the finite-dimensional ODE `u' = νΔu - B(u,u)`, then every Fourier mode of its zero-extension
satisfies the corresponding modewise ODE with a forcing given by the zero-extended nonlinear term.
-/

lemma extendByZero_laplacianCoeff {N : ℕ} (u : GalerkinState N) (k : Mode2) :
    (extendByZero (laplacianCoeff (N := N) u)) k = (-kSq k) • (extendByZero u) k := by
  classical
  by_cases hk : k ∈ modes N
  · ext j
    fin_cases j <;> simp [extendByZero, coeffAt, hk, laplacianCoeff]
  · ext j
    fin_cases j <;> simp [extendByZero, coeffAt, hk]

lemma hasDerivAt_extendByZero_apply {N : ℕ} (k : Mode2)
    (u : ℝ → GalerkinState N) (u' : GalerkinState N) {t : ℝ} (hu : HasDerivAt u u' t) :
    HasDerivAt (fun s : ℝ => (extendByZero (u s)) k) ((extendByZero u') k) t := by
  classical
  -- A constant continuous linear map: project the `k`-th Fourier coefficient after zero-extension.
  let L : GalerkinState N →L[ℝ] VelCoeff :=
    (ContinuousLinearMap.proj k).comp (extendByZeroCLM (N := N))
  have hL : HasDerivAt (fun _ : ℝ => L) 0 t := by
    simpa using (hasDerivAt_const (x := t) (c := L))
  -- Differentiate `s ↦ L (u s)`.
  have h := HasDerivAt.clm_apply (c := fun _ : ℝ => L) (c' := (0 : GalerkinState N →L[ℝ] VelCoeff))
    (u := u) (u' := u') (x := t) hL hu
  -- Unfold `L` back to `extendByZero` + evaluation at `k`.
  simpa [L, extendByZeroCLM] using h

theorem galerkinNS_hasDerivAt_extendByZero_mode {N : ℕ} (ν : ℝ) (B : ConvectionOp N)
    (u : ℝ → GalerkinState N) (k : Mode2) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS (N := N) ν B (u t)) t) :
    HasDerivAt (fun s : ℝ => (extendByZero (u s)) k)
      ((ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k) t := by
  -- Start from the generic differentiation-through-zero-extension lemma.
  have h0 :
      HasDerivAt (fun s : ℝ => (extendByZero (u s)) k)
        ((extendByZero (galerkinNSRHS (N := N) ν B (u t))) k) t :=
    hasDerivAt_extendByZero_apply (N := N) k u (galerkinNSRHS (N := N) ν B (u t)) hu
  -- Simplify the RHS using linearity of `extendByZero` and the diagonal Laplacian.
  -- `extendByZero (ν•Δu - B(u,u)) = ν•extendByZero(Δu) - extendByZero(B(u,u))`
  have hR :
      (extendByZero (galerkinNSRHS (N := N) ν B (u t)) k)
        = (ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k := by
    -- Push `extendByZero` through the RHS definition.
    simp [galerkinNSRHS, extendByZero_smul, extendByZero_add, extendByZero_neg,
      extendByZero_laplacianCoeff, sub_eq_add_neg, mul_smul]
  -- Rewrite the derivative statement with the simplified RHS.
  simpa [hR] using h0

/-!
## Connecting the nonlinear forcing to the Duhamel remainder (modewise, differential form)

We define a *Duhamel remainder* for a Galerkin trajectory by subtracting the linear heat evolution
of the initial coefficient. Then the modewise Galerkin ODE implies a forced linear ODE for this
remainder with forcing given by the zero-extended nonlinear term.

This is not yet the full integral (variation-of-constants) formula, but it ties the remainder to
the Galerkin nonlinearity in a way that can later be integrated.
-/

/-- Duhamel remainder (Galerkin → Fourier, modewise):

`R(t,k) := û(t,k) - heatFactor(ν,t,k) • û(0,k)`. -/
noncomputable def duhamelRemainderOfGalerkin {N : ℕ} (ν : ℝ) (u : ℝ → GalerkinState N) : ℝ → FourierState2D :=
  fun t k => (extendByZero (u t) k) - (heatFactor ν t k) • (extendByZero (u 0) k)

/-- If a Galerkin trajectory satisfies the discrete NS ODE, then its Duhamel remainder satisfies a
forced linear ODE per mode, with forcing `-(extendByZero (B(u,u)))`.

This is the differential version of the Duhamel/variation-of-constants formula. -/
theorem galerkinNS_hasDerivAt_duhamelRemainder_mode {N : ℕ} (ν : ℝ) (B : ConvectionOp N)
    (u : ℝ → GalerkinState N) (k : Mode2) {t : ℝ}
    (hu : HasDerivAt u (galerkinNSRHS (N := N) ν B (u t)) t) :
    HasDerivAt (fun s : ℝ => (duhamelRemainderOfGalerkin (N := N) ν u s) k)
      ((ν * (-kSq k)) • (duhamelRemainderOfGalerkin (N := N) ν u t k) - (extendByZero (B (u t) (u t))) k) t := by
  classical
  -- shorthand
  let a0 : VelCoeff := (extendByZero (u 0)) k

  -- derivative of the main coefficient from the Galerkin ODE
  have ha :
      HasDerivAt (fun s : ℝ => (extendByZero (u s)) k)
        ((ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k) t :=
    galerkinNS_hasDerivAt_extendByZero_mode (N := N) (ν := ν) (B := B) (u := u) (k := k) hu

  -- derivative of the linear heat term `s ↦ heatFactor ν s k • a0`
  have hlin : HasDerivAt (fun s : ℝ => (-ν * kSq k) * s) (-ν * kSq k) t := by
    simpa [mul_assoc] using (hasDerivAt_id t).const_mul (-ν * kSq k)
  have hscalar :
      HasDerivAt (fun s : ℝ => heatFactor ν s k) (heatFactor ν t k * (-ν * kSq k)) t := by
    have hexp :
        HasDerivAt (fun s : ℝ => Real.exp ((-ν * kSq k) * s))
          (Real.exp ((-ν * kSq k) * t) * (-ν * kSq k)) t :=
      (Real.hasDerivAt_exp ((-ν * kSq k) * t)).comp t hlin
    simpa [heatFactor, mul_assoc] using hexp
  have hb :
      HasDerivAt (fun s : ℝ => (heatFactor ν s k) • a0)
        ((heatFactor ν t k * (-ν * kSq k)) • a0) t :=
    hscalar.smul_const a0

  -- differentiate the difference
  have hsub :
      HasDerivAt (fun s : ℝ => (extendByZero (u s)) k - (heatFactor ν s k) • a0)
        (((ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k)
          - ((heatFactor ν t k * (-ν * kSq k)) • a0)) t := by
    -- Do not `simpa` here: we want to keep the derivative expression in a form that
    -- matches the subsequent algebraic rewrite.
    simpa [sub_eq_add_neg] using ha.sub hb

  -- rewrite the derivative into the forced-remainder form
  have hb' :
      (heatFactor ν t k * (-ν * kSq k)) • a0 = (ν * (-kSq k)) • ((heatFactor ν t k) • a0) := by
    calc
      (heatFactor ν t k * (-ν * kSq k)) • a0
          = ((-ν * kSq k) * heatFactor ν t k) • a0 := by
              simp [mul_comm, mul_assoc]
      _ = (-ν * kSq k) • ((heatFactor ν t k) • a0) := by
              simp [mul_smul]
      _ = (ν * (-kSq k)) • ((heatFactor ν t k) • a0) := by ring_nf

  have hderiv_simp :
      (((ν * (-kSq k)) • (extendByZero (u t)) k - (extendByZero (B (u t) (u t))) k)
          - ((heatFactor ν t k * (-ν * kSq k)) • a0))
        = ((ν * (-kSq k)) • ((extendByZero (u t)) k - (heatFactor ν t k) • a0)
            - (extendByZero (B (u t) (u t))) k) := by
    -- push the scalar through the subtraction and use the rewritten `hb'`
    -- First rewrite the heat-term derivative using `hb'`, then reduce to commutative-additive algebra.
    rw [hb']
    -- Expand `c • (x - y)` and rewrite subtraction as addition; then commutativity closes the goal.
    simp [sub_eq_add_neg, add_left_comm, add_comm]

  -- conclude
  have hsub' :
      HasDerivAt (fun s : ℝ => (extendByZero (u s)) k - (heatFactor ν s k) • a0)
        ((ν * (-kSq k)) • ((extendByZero (u t)) k - (heatFactor ν t k) • a0)
          - (extendByZero (B (u t) (u t))) k) t := by
    -- Avoid `simp` rewriting the derivative expression (it tends to normalize `ν * (-kSq)` into `-(ν*kSq)`).
    -- Instead, rewrite the goal using the proved algebraic identity `hderiv_simp`.
    rw [← hderiv_simp]
    exact hsub

  simpa [duhamelRemainderOfGalerkin, a0] using hsub'

/-- Variation-of-constants / Duhamel (integrating factor) formula for the Galerkin remainder (modewise).

This upgrades the forced remainder ODE to an **integral** identity, assuming the forcing term is
interval-integrable.

Note: This is an integrating-factor form; rewriting it into the usual kernel `heatFactor ν (t-s) k`
is a later algebraic step (plus a change-of-variables in the integral). -/
theorem duhamelRemainderOfGalerkin_integratingFactor
    {N : ℕ} (ν : ℝ) (B : ConvectionOp N) (u : ℝ → GalerkinState N) (k : Mode2) (t : ℝ)
    (hu : ∀ s : ℝ, HasDerivAt u (galerkinNSRHS (N := N) ν B (u s)) s)
    (hint :
      IntervalIntegrable (fun s : ℝ =>
        (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k))
        MeasureTheory.volume 0 t) :
    (Real.exp (-(ν * (-kSq k)) * t)) • (duhamelRemainderOfGalerkin (N := N) ν u t k)
      =
        -∫ s in (0 : ℝ)..t, (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k) := by
  classical
  -- Notation
  let a : ℝ := ν * (-kSq k)
  let E : ℝ → ℝ := fun s => Real.exp (-a * s)
  let R : ℝ → VelCoeff := fun s => (duhamelRemainderOfGalerkin (N := N) ν u s) k
  let F : ℝ → VelCoeff := fun s => (extendByZero (B (u s) (u s))) k
  let G : ℝ → VelCoeff := fun s => (E s) • (R s)

  have hE : ∀ x : ℝ, HasDerivAt E (-(E x * a)) x := by
    intro x
    have hlin : HasDerivAt (fun s : ℝ => (-a) * s) (-a) x := by
      simpa [mul_assoc] using (hasDerivAt_id x).const_mul (-a)
    have hexp :
        HasDerivAt (fun s : ℝ => Real.exp ((-a) * s)) (Real.exp ((-a) * x) * (-a)) x :=
      (Real.hasDerivAt_exp ((-a) * x)).comp x hlin
    -- rewrite `r * (-a)` as `-(r * a)`
    simpa [E, mul_assoc, mul_neg] using hexp

  have hR : ∀ x : ℝ, HasDerivAt R (a • R x - F x) x := by
    intro x
    -- Remainder ODE at time `x`
    simpa [R, F, a] using
      (galerkinNS_hasDerivAt_duhamelRemainder_mode (N := N) (ν := ν) (B := B) (u := u) (k := k) (t := x)
        (hu x))

  have hGderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t, HasDerivAt G (-((E x) • (F x))) x := by
    intro x _hx
    have hG0 : HasDerivAt G ((E x) • (a • R x - F x) + (-(E x * a)) • R x) x :=
      (hE x).smul (hR x)
    have hG0' : HasDerivAt G ((E x) • (a • R x - F x) + -((E x * a) • R x)) x := by
      simpa [neg_smul] using hG0
    -- Simplify: the `a • R` terms cancel, leaving `-(E x • F x)`.
    have hsimp :
        (E x) • (a • R x - F x) + -((E x * a) • R x) = -((E x) • (F x)) := by
      -- Expand `E • (a • R - F)` and cancel the `a • R` terms.
      calc
        (E x) • (a • R x - F x) + -((E x * a) • R x)
            = (E x) • (a • R x - F x) - (E x * a) • R x := by
                simp [sub_eq_add_neg]
        _ = (E x) • (a • R x) - (E x) • (F x) - (E x * a) • R x := by
                simp [sub_eq_add_neg, add_assoc]
        _ = (E x * a) • R x - (E x) • (F x) - (E x * a) • R x := by
                simp [smul_smul]
        _ = -((E x) • (F x)) := by abel
    simpa [G, hsimp] using hG0'

  -- Integrate the derivative of `G` on `0..t`.
  have hint' : IntervalIntegrable (fun s : ℝ => -((E s) • (F s))) MeasureTheory.volume 0 t := by
    -- our hypothesis is stated for `Real.exp (-(ν * (-kSq k)) * s)`, which is `E s` by definition
    -- and `F s` is the nonlinear term.
    -- `IntervalIntegrable.neg` handles the outer `-`.
    have : IntervalIntegrable (fun s : ℝ => (E s) • (F s)) MeasureTheory.volume 0 t := by
      simpa [E, F, a] using hint
    simpa using this.neg

  have hFTC :
      (∫ s in (0 : ℝ)..t, -((E s) • (F s))) = G t - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
      (hderiv := hGderiv) (hint := hint')

  have hR0 : R 0 = 0 := by
    -- `R 0 = û(0,k) - heatFactor(0)•û(0,k) = 0`
    simp [R, duhamelRemainderOfGalerkin, heatFactor]

  have hG0 : G 0 = 0 := by
    simp [G, E, hR0]

  -- Rewrite the result in the desired form.
  have hEq : (E t) • (R t) = ∫ s in (0 : ℝ)..t, -((E s) • (F s)) := by
    -- `hFTC` gives the integral equals `G t - G 0`; and `G 0 = 0`.
    have : (∫ s in (0 : ℝ)..t, -((E s) • (F s))) = (E t) • (R t) := by
      simpa [hG0, G] using hFTC
    exact this.symm

  have hEq' : (E t) • (R t) = -∫ s in (0 : ℝ)..t, (E s) • (F s) := by
    calc
      (E t) • (R t) = ∫ s in (0 : ℝ)..t, -((E s) • (F s)) := hEq
      _ = -∫ s in (0 : ℝ)..t, (E s) • (F s) := by simp

  simpa [E, R, F, a] using hEq'

/-- Rewrite the integrating-factor remainder formula into the standard Duhamel kernel form:

`R(t,k) = -∫₀ᵗ heatFactor ν (t - s) k • F(s,k) ds`.

This is a purely algebraic rewrite of `duhamelRemainderOfGalerkin_integratingFactor`. -/
theorem duhamelRemainderOfGalerkin_kernel
    {N : ℕ} (ν : ℝ) (B : ConvectionOp N) (u : ℝ → GalerkinState N) (k : Mode2) (t : ℝ)
    (hu : ∀ s : ℝ, HasDerivAt u (galerkinNSRHS (N := N) ν B (u s)) s)
    (hint :
      IntervalIntegrable (fun s : ℝ =>
        (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k))
        MeasureTheory.volume 0 t) :
    duhamelRemainderOfGalerkin (N := N) ν u t k
      =
        -∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) := by
  -- Start from the integrating-factor identity.
  have hIF :=
    duhamelRemainderOfGalerkin_integratingFactor (N := N) (ν := ν) (B := B) (u := u) (k := k) (t := t) hu hint

  -- Multiply both sides by the heat factor at time `t` to cancel the integrating factor.
  have hmul : (heatFactor ν t k) • ((Real.exp (-(ν * (-kSq k)) * t)) • duhamelRemainderOfGalerkin (N := N) ν u t k)
      =
        (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t,
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k)) := by
    simpa using congrArg (fun v => (heatFactor ν t k) • v) hIF

  -- Simplify the left-hand side: `heatFactor(t) * exp(ν|k|^2 t) = 1`.
  have hcancel :
      (heatFactor ν t k) • ((Real.exp (-(ν * (-kSq k)) * t)) • duhamelRemainderOfGalerkin (N := N) ν u t k)
        = duhamelRemainderOfGalerkin (N := N) ν u t k := by
    -- turn nested smul into product scalar
    have hprod : (heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * t)) = 1 := by
      calc
        (heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * t))
            = Real.exp (-ν * kSq k * t) * Real.exp (ν * kSq k * t) := by
                simp [heatFactor]
        _ = Real.exp ((-ν * kSq k * t) + (ν * kSq k * t)) := (Real.exp_add _ _).symm
        _ = Real.exp 0 := by ring_nf
        _ = 1 := by simp
    calc
      (heatFactor ν t k) • ((Real.exp (-(ν * (-kSq k)) * t)) • duhamelRemainderOfGalerkin (N := N) ν u t k)
          = ((heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * t))) • duhamelRemainderOfGalerkin (N := N) ν u t k := by
              simp [smul_smul]
      _ = (1 : ℝ) • duhamelRemainderOfGalerkin (N := N) ν u t k := by
            -- avoid `simp` rewriting the exponential before applying `hprod`
            rw [hprod]
      _ = duhamelRemainderOfGalerkin (N := N) ν u t k := by simp

  -- Move the scalar inside the integral, then combine the exponentials into `heatFactor ν (t - s) k`.
  have hRHS :
      (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t,
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k))
        =
        -∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) := by
    -- Let `f(s)` be the integrand in the integrating-factor identity.
    let f : ℝ → VelCoeff :=
      fun s => (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k)
    -- First move the scalar inside the integral.
    have hsmul :
        (heatFactor ν t k) • (∫ s in (0 : ℝ)..t, f s) =
          ∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s) := by
      simp [f]
    -- Rewrite `heatFactor ν t k • (-∫ f)` as `-∫ (heatFactor ν t k • f)`.
    have hneg :
        (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t, f s)
          = -∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s) := by
      calc
        (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t, f s)
            = -((heatFactor ν t k) • (∫ s in (0 : ℝ)..t, f s)) := by simp [smul_neg]
        _ = -(∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s)) := by rw [hsmul]
        _ = -∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s) := rfl
    -- Now simplify the integrand pointwise on the integration interval.
    have hEqOn :
        Set.EqOn (fun s => (heatFactor ν t k) • (f s))
          (fun s => (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k)) (Set.uIcc (0 : ℝ) t) := by
      intro s _hs
      -- combine scalar factors into `heatFactor ν (t - s) k`
      have hscalar :
          (heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * s)) = heatFactor ν (t - s) k := by
        calc
          (heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * s))
              = Real.exp (-ν * kSq k * t) * Real.exp (ν * kSq k * s) := by
                  simp [heatFactor]
          _ = Real.exp ((-ν * kSq k * t) + (ν * kSq k * s)) := (Real.exp_add _ _).symm
          _ = Real.exp (-ν * kSq k * (t - s)) := by ring_nf
          _ = heatFactor ν (t - s) k := by simp [heatFactor]
      -- use the scalar identity to rewrite the smul
      calc
        (heatFactor ν t k) • (f s)
            = ((heatFactor ν t k) * (Real.exp (-(ν * (-kSq k)) * s)))
                • (extendByZero (B (u s) (u s)) k) := by
                  simpa [f] using
                    (smul_smul (heatFactor ν t k) (Real.exp (-(ν * (-kSq k)) * s))
                      (extendByZero (B (u s) (u s)) k))
        _ = (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) := by
              -- rewrite the scalar coefficient
              rw [hscalar]
    have hinterr :
        ∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s)
          = ∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) :=
      intervalIntegral.integral_congr (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := t) hEqOn
    -- Finish.
    -- rewrite the integral using `hinterr`
    calc
      (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t, f s)
          = -∫ s in (0 : ℝ)..t, (heatFactor ν t k) • (f s) := hneg
      _ = -∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) := by
            rw [hinterr]

  -- Combine.
  -- use `hcancel` to rewrite the left-hand side, then apply the rewritten right-hand side
  calc
    duhamelRemainderOfGalerkin (N := N) ν u t k
        = (heatFactor ν t k) • ((Real.exp (-(ν * (-kSq k)) * t)) • duhamelRemainderOfGalerkin (N := N) ν u t k) := by
            simpa using hcancel.symm
    _ = (heatFactor ν t k) • (-∫ s in (0 : ℝ)..t,
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k)) := by
            simpa using hmul
    _ = -∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (extendByZero (B (u s) (u s)) k) := hRHS

/-!
## Analytic packaging: dominated convergence for the Duhamel kernel integral

To pass the *time-integrated nonlinear forcing* to the limit, we will eventually need a dominated
convergence / uniform integrability step. We start by packaging the exact hypotheses needed to apply
`intervalIntegral.tendsto_integral_filter_of_dominated_convergence` to the Duhamel kernel integral.

This keeps the proof honest (no `sorry`), while making the missing analytic ingredient explicit.
-/

/-- The Duhamel kernel operator applied to a (Fourier-modewise) forcing trajectory:

`(duhamelKernelIntegral ν F)(t,k) = -∫₀ᵗ heatFactor ν (t-s) k • F(s,k) ds`. -/
noncomputable def duhamelKernelIntegral (ν : ℝ) (F : ℝ → FourierState2D) : ℝ → FourierState2D :=
  fun t k => -∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (F s k)

/-- Hypothesis (at fixed `t,k`): the Duhamel-kernel integrands satisfy the assumptions of dominated
convergence, so the corresponding interval integrals converge. -/
structure DuhamelKernelDominatedConvergenceAt
    (ν : ℝ) (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D)
    (t : ℝ) (k : Mode2) where
  /-- An `L¹` bound for the integrands on `0..t`. -/
  bound : ℝ → ℝ
  /-- Strong measurability (eventually in `N`) on the relevant interval. -/
  h_meas :
    ∀ᶠ N : ℕ in atTop,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => (heatFactor ν (t - s) k) • (F_N N s k))
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
  /-- Dominating bound (eventually in `N`) on the relevant interval. -/
  h_bound :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
        ‖(heatFactor ν (t - s) k) • (F_N N s k)‖ ≤ bound s
  /-- Integrability of the bound. -/
  bound_integrable :
    IntervalIntegrable bound MeasureTheory.volume (0 : ℝ) t
  /-- Pointwise (ae on the interval) convergence of the integrands. -/
  h_lim :
    ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      Tendsto (fun N : ℕ => (heatFactor ν (t - s) k) • (F_N N s k)) atTop
        (𝓝 ((heatFactor ν (t - s) k) • (F s k)))

/-- A more user-facing dominated-convergence hypothesis at fixed `t,k` for the *forcing* itself,
without baking in the Duhamel kernel factor. Under `0 ≤ ν` and `0 ≤ t`, this implies
`DuhamelKernelDominatedConvergenceAt` because `|heatFactor ν (t-s) k| ≤ 1` on `s ∈ Set.uIoc 0 t`. -/
structure ForcingDominatedConvergenceAt
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D) (t : ℝ) (k : Mode2) where
  bound : ℝ → ℝ
  h_meas :
    ∀ᶠ N : ℕ in atTop,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => F_N N s k)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
  h_bound :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t → ‖F_N N s k‖ ≤ bound s
  bound_integrable :
    IntervalIntegrable bound MeasureTheory.volume (0 : ℝ) t
  h_lim :
    ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc (0 : ℝ) t →
      Tendsto (fun N : ℕ => F_N N s k) atTop (𝓝 (F s k))

/-- Heat kernel bound: for `ν ≥ 0` and `τ ≥ 0`, we have `|heatFactor ν τ k| ≤ 1`. -/
lemma abs_heatFactor_le_one (ν : ℝ) (hν : 0 ≤ ν) (τ : ℝ) (hτ : 0 ≤ τ) (k : Mode2) :
    |heatFactor ν τ k| ≤ 1 := by
  -- `heatFactor = exp (-ν * kSq k * τ)` with a nonpositive exponent.
  have hkSq : 0 ≤ kSq k := by simp [kSq, add_nonneg, sq_nonneg]
  have harg : (-ν * kSq k * τ) ≤ 0 := by
    have hprod : 0 ≤ ν * kSq k * τ := mul_nonneg (mul_nonneg hν hkSq) hτ
    -- `-x ≤ 0` for `x ≥ 0`
    have : -(ν * kSq k * τ) ≤ 0 := neg_nonpos.mpr hprod
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hle : heatFactor ν τ k ≤ 1 := by
    simpa [heatFactor] using (Real.exp_le_one_iff.2 harg)
  have hnonneg : 0 ≤ heatFactor ν τ k := (Real.exp_pos _).le
  simpa [abs_of_nonneg hnonneg] using hle

/-- Convenience constructor: it is often easier to assume pointwise statements (`∀`) rather than
almost-everywhere (`∀ᵐ`). This helper upgrades pointwise bounds + convergence to the AE versions
required by `ForcingDominatedConvergenceAt`. -/
noncomputable def ForcingDominatedConvergenceAt.of_forall
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D) (t : ℝ) (k : Mode2)
    (bound : ℝ → ℝ)
    (h_meas : ∀ N : ℕ,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => F_N N s k)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (h_bound : ∀ N : ℕ, ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t → ‖F_N N s k‖ ≤ bound s)
    (bound_integrable : IntervalIntegrable bound MeasureTheory.volume (0 : ℝ) t)
    (h_lim : ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t →
      Tendsto (fun N : ℕ => F_N N s k) atTop (𝓝 (F s k))) :
    ForcingDominatedConvergenceAt (F_N := F_N) (F := F) t k :=
  { bound := bound
    h_meas := Filter.Eventually.of_forall h_meas
    h_bound := by
      refine Filter.Eventually.of_forall ?_
      intro N
      exact MeasureTheory.ae_of_all _ (fun s hs => h_bound N s hs)
    bound_integrable := bound_integrable
    h_lim := by
      exact MeasureTheory.ae_of_all _ (fun s hs => h_lim s hs) }

/-- Convert a forcing-level dominated convergence hypothesis into the kernel-level one. -/
noncomputable def duhamelKernelDominatedConvergenceAt_of_forcing
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    {F_N : ℕ → ℝ → FourierState2D} {F : ℝ → FourierState2D} {k : Mode2}
    (hF : ForcingDominatedConvergenceAt F_N F t k) :
    DuhamelKernelDominatedConvergenceAt ν F_N F t k := by
  classical
  refine
    { bound := hF.bound
      h_meas := ?_
      h_bound := ?_
      bound_integrable := hF.bound_integrable
      h_lim := ?_ }
  · -- measurability: `heatFactor( t - s )` is continuous, and `smul` preserves AE-strong measurability
    have hheat_meas :
        MeasureTheory.AEStronglyMeasurable (fun s : ℝ => heatFactor ν (t - s) k)
          (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
      -- continuity in `s`
      have hcont : Continuous fun s : ℝ => heatFactor ν (t - s) k := by
        -- unfold the scalar kernel and use continuity of `Real.exp`
        -- `s ↦ exp (-ν * kSq k * (t - s))`
        have hlin : Continuous fun s : ℝ => (-ν * kSq k) * (t - s) := by
          exact (continuous_const.mul (continuous_const.sub continuous_id))
        simpa [heatFactor, mul_assoc] using (continuous_exp.comp hlin)
      exact hcont.aestronglyMeasurable
    refine hF.h_meas.mono ?_
    intro N hmeasN
    exact hheat_meas.smul hmeasN
  · -- domination: `|heatFactor| ≤ 1` on `s ∈ uIoc 0 t` (for `t ≥ 0`, `ν ≥ 0`)
    refine hF.h_bound.mono ?_
    intro N hboundN
    filter_upwards [hboundN] with s hsBound
    intro hs
    have hst : 0 < s ∧ s ≤ t := by
      -- unpack membership in the unordered interval
      have hs' : min (0 : ℝ) t < s ∧ s ≤ max (0 : ℝ) t := by
        simpa [Set.uIoc, Set.mem_Ioc] using hs
      simpa [min_eq_left ht, max_eq_right ht] using hs'
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst.2
    have habs : |heatFactor ν (t - s) k| ≤ 1 :=
      abs_heatFactor_le_one ν hν (t - s) hts k
    have hx : ‖F_N N s k‖ ≤ hF.bound s := hsBound hs
    calc
      ‖(heatFactor ν (t - s) k) • (F_N N s k)‖
          = |heatFactor ν (t - s) k| * ‖F_N N s k‖ := by
              simp [Real.norm_eq_abs, norm_smul]
      _ ≤ ‖F_N N s k‖ := by
            simpa [one_mul] using (mul_le_of_le_one_left (norm_nonneg _) habs)
      _ ≤ hF.bound s := hx
  · -- pointwise convergence: multiply by the (fixed-in-`N`) scalar `heatFactor ν (t-s) k`
    filter_upwards [hF.h_lim] with s hsLim
    intro hs
    have hcont : Continuous fun v : VelCoeff => (heatFactor ν (t - s) k) • v := continuous_const_smul _
    exact (hcont.tendsto (F s k)).comp (hsLim hs)

/-- Under the dominated-convergence hypothesis at `t,k`, the Duhamel-kernel integrals converge. -/
theorem tendsto_duhamelKernelIntegral_of_dominated_convergence
    (ν : ℝ) (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D) (t : ℝ) (k : Mode2)
    (hDC : DuhamelKernelDominatedConvergenceAt ν F_N F t k) :
    Tendsto (fun N : ℕ => (duhamelKernelIntegral ν (F_N N) t) k) atTop
      (𝓝 ((duhamelKernelIntegral ν F t) k)) := by
  -- Apply the dominated convergence theorem for interval integrals.
  have hT :
      Tendsto
          (fun N : ℕ =>
            ∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (F_N N s k))
          atTop
          (𝓝 (∫ s in (0 : ℝ)..t, (heatFactor ν (t - s) k) • (F s k))) := by
    simpa using
      (intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := t) (l := atTop)
        (F := fun N : ℕ => fun s : ℝ => (heatFactor ν (t - s) k) • (F_N N s k))
        (f := fun s : ℝ => (heatFactor ν (t - s) k) • (F s k))
        (bound := hDC.bound)
        (hF_meas := hDC.h_meas)
        (h_bound := hDC.h_bound)
        (bound_integrable := hDC.bound_integrable)
        (h_lim := hDC.h_lim))
  -- Move the outer `-` through the limit.
  simpa [duhamelKernelIntegral] using hT.neg

/-- Galerkin modewise Duhamel identity in kernel form:

`û(t,k) = heatFactor ν t k • û(0,k) + duhamelKernelIntegral ν (extendByZero ∘ B(u,u)) (t,k)`.

This is just `duhamelRemainderOfGalerkin_kernel` rewritten using the definition of the remainder. -/
theorem galerkin_duhamelKernel_identity
    {N : ℕ} (ν : ℝ) (B : ConvectionOp N) (u : ℝ → GalerkinState N) (k : Mode2) (t : ℝ)
    (hu : ∀ s : ℝ, HasDerivAt u (galerkinNSRHS (N := N) ν B (u s)) s)
    (hint :
      IntervalIntegrable (fun s : ℝ =>
        (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero (B (u s) (u s)) k))
        MeasureTheory.volume 0 t) :
    (extendByZero (u t) k)
      =
        (heatFactor ν t k) • (extendByZero (u 0) k)
          + (duhamelKernelIntegral ν (fun s : ℝ => extendByZero (B (u s) (u s))) t) k := by
  -- Start from the kernel-form remainder identity.
  have hR :=
    duhamelRemainderOfGalerkin_kernel (N := N) (ν := ν) (B := B) (u := u) (k := k) (t := t) hu hint
  -- Unfold the remainder and rearrange.
  -- `R(t,k) = û(t,k) - heatFactor(t)•û(0,k)` and `R(t,k) = kernelIntegral(t,k)`.
  have :
      (extendByZero (u t) k) - (heatFactor ν t k) • (extendByZero (u 0) k)
        =
          (duhamelKernelIntegral ν (fun s : ℝ => extendByZero (B (u s) (u s))) t) k := by
    simpa [duhamelRemainderOfGalerkin, duhamelKernelIntegral] using hR
  -- Add the heat term to both sides.
  exact (sub_eq_iff_eq_add').1 this

/-!
## A derived bound: single coefficient ≤ global norm

Even before doing any PDE analysis, we can prove a simple but useful fact:
the norm of one Fourier coefficient (after zero-extension) is bounded by the
global Euclidean norm of the truncated Galerkin state.
-/

lemma norm_extendByZero_le {N : ℕ} (u : GalerkinState N) (k : Mode2) :
    ‖(extendByZero u) k‖ ≤ ‖u‖ := by
  classical
  by_cases hk : k ∈ modes N
  ·
    have hext :
        (extendByZero u) k =
          !₂[u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2)),
             u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))] := by
      simp [extendByZero, coeffAt, hk]

    have hsq_ext :
        ‖(extendByZero u) k‖ ^ 2 =
          ‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
            + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2 := by
      -- For `Fin 2`, `EuclideanSpace.norm_sq_eq` expands to the sum of the two coordinate squares.
      simp [hext, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

    have hnorm_u : ‖u‖ ^ 2 = ∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq]

    -- The 2-coordinate sum is bounded by the full coordinate sum.
    have hcoord_le :
        (‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
            + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
          ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := by
      let k' : (modes N) := ⟨k, hk⟩
      let s : Finset ((modes N) × Fin 2) :=
        insert (k', (⟨0, by decide⟩ : Fin 2)) ({(k', (⟨1, by decide⟩ : Fin 2))} : Finset ((modes N) × Fin 2))
      have hs : s ⊆ (Finset.univ : Finset ((modes N) × Fin 2)) := by
        intro x hx
        simp
      have hsum :
          (‖u (k', (⟨0, by decide⟩ : Fin 2))‖ ^ 2 + ‖u (k', (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
            = (∑ kc ∈ s, ‖u kc‖ ^ 2) := by
        simp [s]
      have hle : (∑ kc ∈ s, ‖u kc‖ ^ 2) ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := by
        have hle' :
            (∑ kc ∈ s, ‖u kc‖ ^ 2)
              ≤ (∑ kc ∈ (Finset.univ : Finset ((modes N) × Fin 2)), ‖u kc‖ ^ 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hs ?_
          intro kc _hkc _hknot
          exact sq_nonneg ‖u kc‖
        simpa using hle'
      calc
        (‖u (k', (⟨0, by decide⟩ : Fin 2))‖ ^ 2 + ‖u (k', (⟨1, by decide⟩ : Fin 2))‖ ^ 2)
            = (∑ kc ∈ s, ‖u kc‖ ^ 2) := hsum
        _ ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := hle

    have hsq_le : ‖(extendByZero u) k‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      calc
        ‖(extendByZero u) k‖ ^ 2
            = (‖u (⟨k, hk⟩, (⟨0, by decide⟩ : Fin 2))‖ ^ 2
                + ‖u (⟨k, hk⟩, (⟨1, by decide⟩ : Fin 2))‖ ^ 2) := hsq_ext
        _ ≤ (∑ kc : ((modes N) × Fin 2), ‖u kc‖ ^ 2) := hcoord_le
        _ = ‖u‖ ^ 2 := by simp [hnorm_u]

    exact le_of_sq_le_sq hsq_le (norm_nonneg u)
  ·
    -- Outside the truncation window the coefficient is zero, so the bound is trivial.
    have hnorm : ‖(extendByZero u) k‖ = 0 := by
      simp [extendByZero, coeffAt, hk]
    simp [hnorm, norm_nonneg u]

/-!
## Compactness + identification as explicit hypotheses
-/

/-- Hypothesis: uniform-in-`N` bounds for a *family* of Galerkin trajectories `uN`.

In a real proof this would come from:
- discrete energy/enstrophy inequalities,
- CPM coercivity/dispersion bounds, and
- compactness tools (Aubin–Lions / Banach–Alaoglu / etc.).
-/
structure UniformBoundsHypothesis where
  /-- Discrete Galerkin trajectories at each truncation level `N`. -/
  uN : (N : ℕ) → ℝ → GalerkinState N
  /-- A global (in time, and uniform in `N`) bound. -/
  B : ℝ
  B_nonneg : 0 ≤ B
  /-- Uniform bound: for all `N` and all `t ≥ 0`, `‖uN N t‖ ≤ B`. -/
  bound : ∀ N : ℕ, ∀ t ≥ 0, ‖uN N t‖ ≤ B

/-- Build `UniformBoundsHypothesis` from the *viscous* Galerkin energy estimate, provided we have
an initial uniform bound `‖uN N 0‖ ≤ B` across all truncation levels.
-/
noncomputable def UniformBoundsHypothesis.ofViscous
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (HB : ∀ N : ℕ, EnergySkewHypothesis (Bop N))
    (u : (N : ℕ) → ℝ → GalerkinState N)
    (hu : ∀ N : ℕ, ∀ t : ℝ, HasDerivAt (u N) (galerkinNSRHS ν (Bop N) ((u N) t)) t)
    (B : ℝ) (B_nonneg : 0 ≤ B)
    (h0 : ∀ N : ℕ, ‖u N 0‖ ≤ B) :
    UniformBoundsHypothesis :=
  { uN := u
    B := B
    B_nonneg := B_nonneg
    bound := by
      intro N t ht
      have hNt : ‖u N t‖ ≤ ‖u N 0‖ :=
        viscous_norm_bound_from_initial (N := N) ν hν (Bop N) (HB N) (u N) (hu N) t ht
      exact le_trans hNt (h0 N) }

/-- The (Galerkin) nonlinear forcing family in full Fourier variables:

`F_N(N,s) := extendByZero (Bop N (uN N s) (uN N s))`. -/
noncomputable def galerkinForcing (H : UniformBoundsHypothesis) (Bop : (N : ℕ) → ConvectionOp N) :
    ℕ → ℝ → FourierState2D :=
  fun N s => extendByZero ((Bop N) (H.uN N s) (H.uN N s))

/-- A more concrete, user-facing hypothesis for dominated convergence of the *Galerkin forcing*
`galerkinForcing H Bop`, expressed directly in terms of:

- measurability of the forcing modes,
- an integrable dominating function on each time interval `[0,t]`, and
- pointwise convergence of forcing modes.

This packages exactly what you need to build `ForcingDominatedConvergenceAt` for the Galerkin forcing. -/
structure GalerkinForcingDominatedConvergenceHypothesis
    (H : UniformBoundsHypothesis) (Bop : (N : ℕ) → ConvectionOp N) where
  /-- Limiting forcing in full Fourier variables. -/
  F : ℝ → FourierState2D
  /-- Dominating `L¹` bound, allowed to depend on `(t,k)`. -/
  bound : ℝ → Mode2 → ℝ → ℝ
  /-- Integrability of the dominating bound on each interval `0..t` (for `t ≥ 0`). -/
  bound_integrable : ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2,
    IntervalIntegrable (bound t k) MeasureTheory.volume (0 : ℝ) t
  /-- Strong measurability (in `s`) of each forcing mode on `0..t` (for `t ≥ 0`). -/
  meas : ∀ N : ℕ, ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2,
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (galerkinForcing H Bop N s) k)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t))
  /-- Pointwise domination by the integrable bound on `0..t` (for `t ≥ 0`). -/
  dom : ∀ N : ℕ, ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t →
    ‖(galerkinForcing H Bop N s) k‖ ≤ bound t k s
  /-- Pointwise convergence of forcing modes on `0..t` (for `t ≥ 0`). -/
  lim : ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t →
    Tendsto (fun N : ℕ => (galerkinForcing H Bop N s) k) atTop (𝓝 ((F s) k))

namespace GalerkinForcingDominatedConvergenceHypothesis

/-- Build `ForcingDominatedConvergenceAt` for the Galerkin forcing from the more concrete hypothesis
`GalerkinForcingDominatedConvergenceHypothesis`. -/
noncomputable def forcingDCTAt
    {H : UniformBoundsHypothesis} {Bop : (N : ℕ) → ConvectionOp N}
    (hF : GalerkinForcingDominatedConvergenceHypothesis H Bop)
    (t : ℝ) (ht : 0 ≤ t) (k : Mode2) :
    ForcingDominatedConvergenceAt (F_N := galerkinForcing H Bop) (F := hF.F) t k :=
  ForcingDominatedConvergenceAt.of_forall (F_N := galerkinForcing H Bop) (F := hF.F) (t := t) (k := k)
    (bound := hF.bound t k)
    (h_meas := by intro N; exact hF.meas N t ht k)
    (h_bound := by intro N s hs; exact hF.dom N t ht k s hs)
    (bound_integrable := hF.bound_integrable t ht k)
    (h_lim := by intro s hs; exact hF.lim t ht k s hs)

/-- If each Galerkin trajectory `uN N` is continuous and each `Bop N` is continuous as a map
`(u,v) ↦ Bop N u v`, then each forcing mode `s ↦ (galerkinForcing H Bop N s) k` is continuous (hence
AE-strongly measurable on any finite interval). -/
theorem aestronglyMeasurable_galerkinForcing_mode_of_continuous
    (H : UniformBoundsHypothesis) (Bop : (N : ℕ) → ConvectionOp N)
    (hBcont : ∀ N : ℕ,
      Continuous (fun p : GalerkinState N × GalerkinState N => (Bop N) p.1 p.2))
    (hucont : ∀ N : ℕ, Continuous (H.uN N))
    (N : ℕ) (t : ℝ) (_ht : 0 ≤ t) (k : Mode2) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => (galerkinForcing H Bop N s) k)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)) := by
  -- Continuity of `s ↦ Bop N (uN N s) (uN N s)`.
  have hpair : Continuous fun s : ℝ => (H.uN N s, H.uN N s) := by
    -- build continuity from `ContinuousAt.prodMk`
    refine continuous_iff_continuousAt.2 ?_
    intro s
    simpa using
      (ContinuousAt.prodMk (x := s) ((hucont N).continuousAt) ((hucont N).continuousAt))
  have hB : Continuous fun s : ℝ => (Bop N) (H.uN N s) (H.uN N s) :=
    (hBcont N).comp hpair
  -- Apply the continuous linear map `u ↦ (extendByZero u) k`.
  let L : GalerkinState N →L[ℝ] VelCoeff :=
    (ContinuousLinearMap.proj k).comp (extendByZeroCLM (N := N))
  have hL : Continuous fun u : GalerkinState N => L u := L.continuous
  have hcoeff : Continuous fun s : ℝ => (galerkinForcing H Bop N s) k := by
    -- unfold back to `extendByZero` + evaluation at `k`
    simpa [galerkinForcing, L, extendByZeroCLM] using hL.comp hB
  exact hcoeff.aestronglyMeasurable

/-- Sufficient condition: a **uniform norm bound** on the convection term plus the uniform-in-time
bound `‖uN‖ ≤ B` yields an integrable domination for every forcing mode.

This discharges the `bound_integrable` and `dom` fields of `GalerkinForcingDominatedConvergenceHypothesis`,
leaving only measurability + pointwise forcing convergence as hypotheses. -/
noncomputable def of_convectionNormBound
    (H : UniformBoundsHypothesis) (Bop : (N : ℕ) → ConvectionOp N)
    (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, ∀ u : GalerkinState N, ‖(Bop N u u)‖ ≤ C * ‖u‖ ^ 2)
    (F : ℝ → FourierState2D)
    (meas : ∀ N : ℕ, ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2,
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => (galerkinForcing H Bop N s) k)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) t)))
    (lim : ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t →
      Tendsto (fun N : ℕ => (galerkinForcing H Bop N s) k) atTop (𝓝 ((F s) k))) :
    GalerkinForcingDominatedConvergenceHypothesis H Bop :=
by
  classical
  refine
    { F := F
      bound := fun _t _k _s => C * H.B ^ 2
      bound_integrable := by
        intro t _ht k
        -- constant function is interval integrable on any finite interval
        simp
      meas := meas
      dom := ?_
      lim := lim }
  intro N t ht k s hs
  -- from `s ∈ uIoc 0 t` and `0 ≤ t`, we have `0 < s` hence `0 ≤ s`.
  have hs' : 0 < s ∧ s ≤ t := by
    have hs'' : min (0 : ℝ) t < s ∧ s ≤ max (0 : ℝ) t := by
      simpa [Set.uIoc, Set.mem_Ioc] using hs
    simpa [min_eq_left ht, max_eq_right ht] using hs''
  have hs0 : 0 ≤ s := le_of_lt hs'.1

  -- uniform bound on `uN`
  have hu : ‖H.uN N s‖ ≤ H.B := H.bound N s hs0

  -- square the bound: `‖u‖^2 ≤ B^2`
  have hu_sq : ‖H.uN N s‖ ^ 2 ≤ H.B ^ 2 := by
    have : ‖H.uN N s‖ * ‖H.uN N s‖ ≤ H.B * H.B :=
      mul_le_mul hu hu (norm_nonneg _) H.B_nonneg
    simpa [pow_two] using this

  -- control the Galerkin nonlinearity in norm, then pass to a single Fourier coefficient
  have hBuu : ‖(Bop N (H.uN N s) (H.uN N s))‖ ≤ C * ‖H.uN N s‖ ^ 2 :=
    hB N (H.uN N s)
  have hBuu' : ‖(Bop N (H.uN N s) (H.uN N s))‖ ≤ C * H.B ^ 2 :=
    le_trans hBuu (mul_le_mul_of_nonneg_left hu_sq hC)
  have hcoeff :
      ‖(galerkinForcing H Bop N s) k‖ ≤ C * H.B ^ 2 := by
    have h1 :
        ‖(galerkinForcing H Bop N s) k‖ ≤ ‖(Bop N (H.uN N s) (H.uN N s))‖ := by
      simpa [galerkinForcing] using
        (norm_extendByZero_le (u := (Bop N (H.uN N s) (H.uN N s))) (k := k))
    exact le_trans h1 hBuu'
  simpa using hcoeff

/-- Combine `of_convectionNormBound` with continuity assumptions to discharge measurability of the
Galerkin forcing modes automatically. -/
noncomputable def of_convectionNormBound_of_continuous
    (H : UniformBoundsHypothesis) (Bop : (N : ℕ) → ConvectionOp N)
    (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, ∀ u : GalerkinState N, ‖(Bop N u u)‖ ≤ C * ‖u‖ ^ 2)
    (hBcont : ∀ N : ℕ,
      Continuous (fun p : GalerkinState N × GalerkinState N => (Bop N) p.1 p.2))
    (hucont : ∀ N : ℕ, Continuous (H.uN N))
    (F : ℝ → FourierState2D)
    (lim : ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ∀ s : ℝ, s ∈ Set.uIoc (0 : ℝ) t →
      Tendsto (fun N : ℕ => (galerkinForcing H Bop N s) k) atTop (𝓝 ((F s) k))) :
    GalerkinForcingDominatedConvergenceHypothesis H Bop :=
  of_convectionNormBound (H := H) (Bop := Bop) (C := C) hC (hB := hB) (F := F)
    (meas := by
      intro N t ht k
      exact aestronglyMeasurable_galerkinForcing_mode_of_continuous (H := H) (Bop := Bop)
        (hBcont := hBcont) (hucont := hucont) N t ht k)
    (lim := lim)

end GalerkinForcingDominatedConvergenceHypothesis

/-- Hypothesis: existence of a limit Fourier trajectory and convergence from the approximants. -/
structure ConvergenceHypothesis (H : UniformBoundsHypothesis) where
  /-- Candidate limit (time → full Fourier coefficients). -/
  u : ℝ → FourierState2D
  /-- Pointwise (mode-by-mode) convergence of the zero-extended Galerkin coefficients. -/
  converges : ∀ t : ℝ, ∀ k : Mode2,
    Tendsto (fun N : ℕ => (extendByZero (H.uN N t)) k) atTop (𝓝 ((u t) k))

namespace ConvergenceHypothesis

/-- Derived fact: if the approximants are uniformly bounded in the Galerkin norm for `t ≥ 0`,
then the limit coefficients inherit the same bound (by closedness of `closedBall`). -/
theorem coeff_bound_of_uniformBounds {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    ∀ t ≥ 0, ∀ k : Mode2, ‖(HC.u t) k‖ ≤ H.B := by
  intro t ht k
  -- Put every approximant coefficient inside the closed ball of radius `B`.
  have hmem :
      ∀ N : ℕ, (extendByZero (H.uN N t) k) ∈ Metric.closedBall (0 : VelCoeff) H.B := by
    intro N
    have h1 : ‖(extendByZero (H.uN N t)) k‖ ≤ ‖H.uN N t‖ :=
      norm_extendByZero_le (u := H.uN N t) (k := k)
    have h2 : ‖H.uN N t‖ ≤ H.B := H.bound N t ht
    have h3 : ‖(extendByZero (H.uN N t)) k‖ ≤ H.B := le_trans h1 h2
    -- `Metric.mem_closedBall` is `dist ≤ radius`, and `dist x 0 = ‖x‖`.
    simpa [Metric.mem_closedBall, dist_zero_right] using h3

  have hmem_event :
      (∀ᶠ N : ℕ in atTop, (extendByZero (H.uN N t) k) ∈ Metric.closedBall (0 : VelCoeff) H.B) :=
    Filter.Eventually.of_forall hmem

  have hlim_mem :
      (HC.u t) k ∈ Metric.closedBall (0 : VelCoeff) H.B :=
    IsClosed.mem_of_tendsto (b := atTop) Metric.isClosed_closedBall (HC.converges t k) hmem_event

  have : dist ((HC.u t) k) (0 : VelCoeff) ≤ H.B :=
    (Metric.mem_closedBall).1 hlim_mem

  simpa [dist_zero_right] using this

/-- If the approximants satisfy the (Fourier) divergence constraint at a fixed `t,k`, then so does
the limit coefficient (by continuity + uniqueness of limits in `ℝ`). -/
theorem divConstraint_eq_zero_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (t : ℝ) (k : Mode2)
    (hDF : ∀ N : ℕ, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    divConstraint k ((HC.u t) k) = 0 := by
  -- Push convergence through the continuous map `divConstraint k`.
  have hT :
      Tendsto (fun N : ℕ => divConstraint k ((extendByZero (H.uN N t)) k)) atTop
        (𝓝 (divConstraint k ((HC.u t) k))) := by
    have hcont : Continuous (fun v : VelCoeff => divConstraint k v) := divConstraint_continuous k
    have hcontT :
        Tendsto (fun v : VelCoeff => divConstraint k v) (𝓝 ((HC.u t) k))
          (𝓝 (divConstraint k ((HC.u t) k))) :=
      hcont.tendsto ((HC.u t) k)
    exact hcontT.comp (HC.converges t k)

  -- The sequence is constantly 0 by assumption.
  have heq : (fun N : ℕ => divConstraint k ((extendByZero (H.uN N t)) k)) = fun _ : ℕ => (0 : ℝ) := by
    funext N
    simpa using (hDF N)

  have hT0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (divConstraint k ((HC.u t) k))) := by
    simpa [heq] using hT
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds

  exact tendsto_nhds_unique hT0 hconst

/-- Divergence-free passes to the limit under modewise convergence, assuming each approximant is
divergence-free (in the Fourier-side sense) at every time. -/
theorem divFree_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (hDF : ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    IsDivergenceFreeTraj HC.u := by
  intro t k
  exact divConstraint_eq_zero_of_forall (HC := HC) (t := t) (k := k) (hDF := fun N => hDF N t k)

/-- Mild Stokes/heat identity passes to the limit under modewise convergence,
assuming it holds for every approximant (modewise, for `t ≥ 0`). -/
theorem stokesMild_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) = (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) :
    IsStokesMildTraj ν HC.u := by
  intro t ht k
  -- convergence at time t and at time 0
  have hconv_t : Tendsto (fun N : ℕ => extendByZero (H.uN N t) k) atTop (nhds ((HC.u t) k)) :=
    HC.converges t k
  have hconv_0 : Tendsto (fun N : ℕ => extendByZero (H.uN N 0) k) atTop (nhds ((HC.u 0) k)) :=
    HC.converges 0 k
  -- push convergence at time 0 through the continuous map `v ↦ heatFactor • v`
  have hsmul :
      Tendsto (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) atTop
        (nhds ((heatFactor ν t k) • ((HC.u 0) k))) := by
    have hcont : Continuous fun v : VelCoeff => (heatFactor ν t k) • v := continuous_const_smul _
    exact (hcont.tendsto ((HC.u 0) k)).comp hconv_0
  -- but the two sequences are equal for all N (by hypothesis), hence have the same limit
  have hEq :
      (fun N : ℕ => extendByZero (H.uN N t) k)
        =ᶠ[atTop] (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    exact hMild N t ht k
  -- uniqueness of limits in a T2 space
  have : (HC.u t) k = (heatFactor ν t k) • ((HC.u 0) k) :=
    tendsto_nhds_unique_of_eventuallyEq hconv_t hsmul hEq
  simpa using this

/-- Duhamel-remainder identity passes to the limit under modewise convergence,
assuming it holds for every approximant with remainders `D_N` that converge modewise. -/
theorem nsDuhamel_of_forall {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (D_N : ℕ → ℝ → FourierState2D) (D : ℝ → FourierState2D)
    (hD : ∀ t : ℝ, ∀ k : Mode2,
      Tendsto (fun N : ℕ => (D_N N t) k) atTop (nhds ((D t) k)))
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (D_N N t) k) :
    IsNSDuhamelTraj ν D HC.u := by
  intro t ht k
  -- convergence of the main trajectory at time `t` and at time `0`
  have hconv_t : Tendsto (fun N : ℕ => extendByZero (H.uN N t) k) atTop (nhds ((HC.u t) k)) :=
    HC.converges t k
  have hconv_0 : Tendsto (fun N : ℕ => extendByZero (H.uN N 0) k) atTop (nhds ((HC.u 0) k)) :=
    HC.converges 0 k
  -- convergence of the remainder term
  have hconv_D : Tendsto (fun N : ℕ => (D_N N t) k) atTop (nhds ((D t) k)) :=
    hD t k
  -- push convergence at time 0 through the continuous map `v ↦ heatFactor • v`
  have hsmul :
      Tendsto (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) atTop
        (nhds ((heatFactor ν t k) • ((HC.u 0) k))) := by
    have hcont : Continuous fun v : VelCoeff => (heatFactor ν t k) • v := continuous_const_smul _
    exact (hcont.tendsto ((HC.u 0) k)).comp hconv_0
  -- combine the smul part and the remainder part
  have hsum :
      Tendsto (fun N : ℕ =>
        (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (D_N N t) k) atTop
          (nhds ((heatFactor ν t k) • ((HC.u 0) k) + (D t) k)) :=
    hsmul.add hconv_D
  -- the identity holds for every N, hence the two sequences are eventually equal
  have hEq :
      (fun N : ℕ => extendByZero (H.uN N t) k)
        =ᶠ[atTop] (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (D_N N t) k) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    exact hId N t ht k
  -- uniqueness of limits in a T2 space
  have :
      (HC.u t) k = (heatFactor ν t k) • ((HC.u 0) k) + (D t) k :=
    tendsto_nhds_unique_of_eventuallyEq hconv_t hsum hEq
  simpa [IsNSDuhamelTraj] using this

/-- Convenience wrapper around `nsDuhamel_of_forall` when the remainder terms are defined as Duhamel
kernel integrals and convergence is supplied via dominated convergence (hypothesis-level). -/
theorem nsDuhamel_of_forall_kernelIntegral {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D)
    (hDC : ∀ t : ℝ, ∀ k : Mode2, DuhamelKernelDominatedConvergenceAt ν F_N F t k)
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k) :
    IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) HC.u := by
  have hD :
      ∀ t : ℝ, ∀ k : Mode2,
        Tendsto (fun N : ℕ => (duhamelKernelIntegral ν (F_N N) t) k) atTop
          (nhds (((duhamelKernelIntegral ν F) t) k)) := by
    intro t k
    exact tendsto_duhamelKernelIntegral_of_dominated_convergence (ν := ν) (F_N := F_N) (F := F) (t := t) (k := k)
      (hDC t k)
  exact
    nsDuhamel_of_forall (HC := HC) (ν := ν)
      (D_N := fun N => duhamelKernelIntegral ν (F_N N)) (D := duhamelKernelIntegral ν F)
      (hD := hD) (hId := hId)

/-- Variant of `nsDuhamel_of_forall_kernelIntegral` that assumes dominated convergence only for the
*forcing* (not the kernel integrand), plus `0 ≤ ν` and `t ≥ 0` to control the kernel factor. -/
theorem nsDuhamel_of_forall_kernelIntegral_of_forcing {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (ν : ℝ) (hν : 0 ≤ ν)
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D)
    (hF :
      ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ForcingDominatedConvergenceAt (F_N := F_N) (F := F) t k)
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k) :
    IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) HC.u := by
  intro t ht k
  -- convergence of the main trajectory at time `t` and at time `0`
  have hconv_t : Tendsto (fun N : ℕ => extendByZero (H.uN N t) k) atTop (nhds ((HC.u t) k)) :=
    HC.converges t k
  have hconv_0 : Tendsto (fun N : ℕ => extendByZero (H.uN N 0) k) atTop (nhds ((HC.u 0) k)) :=
    HC.converges 0 k
  -- convergence of the kernel-integral remainder at time `t` (from forcing-level DCT)
  have hconv_D :
      Tendsto (fun N : ℕ => (duhamelKernelIntegral ν (F_N N) t) k) atTop
        (nhds (((duhamelKernelIntegral ν F) t) k)) := by
    have hDC : DuhamelKernelDominatedConvergenceAt ν F_N F t k :=
      duhamelKernelDominatedConvergenceAt_of_forcing (ν := ν) (t := t) hν ht (hF t ht k)
    exact
      tendsto_duhamelKernelIntegral_of_dominated_convergence (ν := ν) (F_N := F_N) (F := F) (t := t) (k := k)
        hDC
  -- push convergence at time 0 through the continuous map `v ↦ heatFactor • v`
  have hsmul :
      Tendsto (fun N : ℕ => (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) atTop
        (nhds ((heatFactor ν t k) • ((HC.u 0) k))) := by
    have hcont : Continuous fun v : VelCoeff => (heatFactor ν t k) • v := continuous_const_smul _
    exact (hcont.tendsto ((HC.u 0) k)).comp hconv_0
  -- combine the smul part and the remainder part
  have hsum :
      Tendsto (fun N : ℕ =>
        (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (duhamelKernelIntegral ν (F_N N) t) k) atTop
          (nhds ((heatFactor ν t k) • ((HC.u 0) k) + ((duhamelKernelIntegral ν F) t) k)) :=
    hsmul.add hconv_D
  -- the identity holds for every N, hence the two sequences are eventually equal
  have hEq :
      (fun N : ℕ => extendByZero (H.uN N t) k)
        =ᶠ[atTop]
          (fun N : ℕ =>
            (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (duhamelKernelIntegral ν (F_N N) t) k) := by
    refine Filter.Eventually.of_forall ?_
    intro N
    exact hId N t ht k
  -- uniqueness of limits in a T2 space
  have :
      (HC.u t) k = (heatFactor ν t k) • ((HC.u 0) k) + ((duhamelKernelIntegral ν F) t) k :=
    tendsto_nhds_unique_of_eventuallyEq hconv_t hsum hEq
  simpa [IsNSDuhamelTraj] using this

end ConvergenceHypothesis

/-- Convenience constructor: if each coefficient sequence is *eventually equal* to the corresponding
limit coefficient, then it tends to that limit. -/
noncomputable def ConvergenceHypothesis.ofEventuallyEq
    (H : UniformBoundsHypothesis)
    (u : ℝ → FourierState2D)
    (heq :
      ∀ t : ℝ, ∀ k : Mode2,
        (fun N : ℕ => (extendByZero (H.uN N t)) k) =ᶠ[atTop] (fun _ : ℕ => (u t) k)) :
    ConvergenceHypothesis H :=
  { u := u
    converges := by
      intro t k
      have hconst : Tendsto (fun _ : ℕ => (u t) k) atTop (𝓝 ((u t) k)) :=
        tendsto_const_nhds
      exact (tendsto_congr' (heq t k)).2 hconst }

/-- Hypothesis: the limit object satisfies the intended PDE identity (kept abstract here). -/
structure IdentificationHypothesis {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) where
  /-- A (later: concrete) solution concept for 2D Navier–Stokes on the torus. -/
  IsSolution : (ℝ → FourierState2D) → Prop
  /-- Proof that the limit trajectory satisfies the chosen solution concept. -/
  isSolution : IsSolution HC.u

namespace IdentificationHypothesis

/-- Trivial identification constructor: choose `IsSolution := True`. -/
def trivial {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    IdentificationHypothesis HC :=
  { IsSolution := fun _ => True
    isSolution := by trivial }

/-- Concrete (but still minimal) identification: define `IsSolution u` to mean the limit coefficients
are uniformly bounded by the Galerkin bound `H.B` for `t ≥ 0`.

This is **provable** from `UniformBoundsHypothesis` + modewise convergence (no extra analytic input),
via `ConvergenceHypothesis.coeff_bound_of_uniformBounds`.
-/
def coeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u => ∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B
    isSolution := by
      intro t ht k
      simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k) }

/-- Identification constructor: coefficient bound + divergence-free (Fourier-side).

The coefficient bound part is proved from `UniformBoundsHypothesis` + convergence.
The divergence-free part is proved from the extra assumption that *each approximant* is divergence-free.
-/
def divFreeCoeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (hDF : ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2, divConstraint k ((extendByZero (H.uN N t)) k) = 0) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsDivergenceFreeTraj u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · intro t k
        exact ConvergenceHypothesis.divConstraint_eq_zero_of_forall (HC := HC) (t := t) (k := k)
          (hDF := fun N => hDF N t k) }

/-- Identification constructor: coefficient bound + (linear) Stokes/heat mild identity.

The bound part is proved from `UniformBoundsHypothesis` + convergence.
The mild Stokes identity is proved from the extra assumption that it holds for every approximant. -/
def stokesMildCoeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (hMild :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) = (heatFactor ν t k) • (extendByZero (H.uN N 0) k)) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsStokesMildTraj ν u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · exact ConvergenceHypothesis.stokesMild_of_forall (HC := HC) (ν := ν) hMild }

/-- Identification constructor: coefficient bound + a first nonlinear (Duhamel-style) remainder identity.

The coefficient bound part is proved from `UniformBoundsHypothesis` + convergence.
The Duhamel-remainder identity is proved from the extra assumptions:

- each approximant satisfies `extendByZero uN(t,k) = heatFactor • extendByZero uN(0,k) + D_N(t,k)`, and
- `D_N(t,k) → D(t,k)` modewise.

In later milestones, `D_N` will be instantiated as an actual time-integrated nonlinear forcing term. -/
def nsDuhamelCoeffBound {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (D_N : ℕ → ℝ → FourierState2D) (D : ℝ → FourierState2D)
    (hD : ∀ t : ℝ, ∀ k : Mode2,
      Tendsto (fun N : ℕ => (D_N N t) k) atTop (nhds ((D t) k)))
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k) + (D_N N t) k) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsNSDuhamelTraj ν D u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · exact ConvergenceHypothesis.nsDuhamel_of_forall (HC := HC) (ν := ν) (D_N := D_N) (D := D) hD hId }

/-- Identification constructor: coefficient bound + Duhamel remainder identity where the remainder is
defined as a **kernel integral** of a forcing term, and convergence of the kernel integrals is
packaged via `DuhamelKernelDominatedConvergenceAt`. -/
def nsDuhamelCoeffBound_kernelIntegral {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D)
    (hDC : ∀ t : ℝ, ∀ k : Mode2, DuhamelKernelDominatedConvergenceAt ν F_N F t k)
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · exact
          ConvergenceHypothesis.nsDuhamel_of_forall_kernelIntegral (HC := HC) (ν := ν)
            (F_N := F_N) (F := F) hDC hId }

/-- Same as `nsDuhamelCoeffBound_kernelIntegral`, but assumes dominated convergence at the **forcing**
level (not the kernel integrand), plus `0 ≤ ν`. -/
def nsDuhamelCoeffBound_kernelIntegral_of_forcing {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (ν : ℝ) (hν : 0 ≤ ν)
    (F_N : ℕ → ℝ → FourierState2D) (F : ℝ → FourierState2D)
    (hF :
      ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2, ForcingDominatedConvergenceAt (F_N := F_N) (F := F) t k)
    (hId :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k) :
    IdentificationHypothesis HC :=
  { IsSolution := fun u =>
      (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) ∧ IsNSDuhamelTraj ν (duhamelKernelIntegral ν F) u
    isSolution := by
      refine ⟨?_, ?_⟩
      · intro t ht k
        simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)
      · exact
          ConvergenceHypothesis.nsDuhamel_of_forall_kernelIntegral_of_forcing (HC := HC)
            (ν := ν) hν (F_N := F_N) (F := F) hF hId }

/-- Identification constructor: a specialization of `nsDuhamelCoeffBound_kernelIntegral` where the
forcing family is the **actual Galerkin nonlinearity** `extendByZero (B(u_N,u_N))`. The Duhamel
identity for each approximant is discharged by `galerkin_duhamelKernel_identity`; the remaining
analytic ingredient is the dominated-convergence hypothesis `hDC`. -/
def nsDuhamelCoeffBound_galerkinKernel {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H) (ν : ℝ)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (H.uN N) (galerkinNSRHS (N := N) ν (Bop N) (H.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (H.uN N s) (H.uN N s)) k))
          MeasureTheory.volume 0 t)
    (F : ℝ → FourierState2D)
    (hDC :
      ∀ t : ℝ, ∀ k : Mode2,
        DuhamelKernelDominatedConvergenceAt ν
          (fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (H.uN N s) (H.uN N s))) F t k) :
    IdentificationHypothesis HC := by
  -- Define the forcing family from the Galerkin nonlinearity.
  let F_N : ℕ → ℝ → FourierState2D :=
    fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (H.uN N s) (H.uN N s))
  -- The approximant Duhamel identity follows from the Galerkin kernel lemma.
  have hId' :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k := by
    intro N t _ht k
    -- `galerkin_duhamelKernel_identity` does not require `t ≥ 0`, but we only need it on that domain.
    simpa [F_N] using
      (galerkin_duhamelKernel_identity (N := N) (ν := ν) (B := Bop N) (u := H.uN N) (k := k) (t := t)
        (hu := fun s => hu N s) (hint := hint N t k))
  -- Reduce to the kernel-integral constructor.
  refine nsDuhamelCoeffBound_kernelIntegral (HC := HC) (ν := ν) (F_N := F_N) (F := F) ?_ hId'
  intro t k
  simpa [F_N] using hDC t k

/-- Same as `nsDuhamelCoeffBound_galerkinKernel`, but assumes dominated convergence at the **forcing**
level (not the kernel integrand), plus `0 ≤ ν`. -/
def nsDuhamelCoeffBound_galerkinKernel_of_forcing {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (H.uN N) (galerkinNSRHS (N := N) ν (Bop N) (H.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (H.uN N s) (H.uN N s)) k))
          MeasureTheory.volume 0 t)
    (F : ℝ → FourierState2D)
    (hF :
      ∀ t : ℝ, t ≥ 0 → ∀ k : Mode2,
        ForcingDominatedConvergenceAt
          (F_N := fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (H.uN N s) (H.uN N s)))
          (F := F) t k) :
    IdentificationHypothesis HC := by
  -- Define the forcing family from the Galerkin nonlinearity.
  let F_N : ℕ → ℝ → FourierState2D :=
    fun N : ℕ => fun s : ℝ => extendByZero ((Bop N) (H.uN N s) (H.uN N s))
  -- The approximant Duhamel identity follows from the Galerkin kernel lemma.
  have hId' :
      ∀ N : ℕ, ∀ t ≥ 0, ∀ k : Mode2,
        (extendByZero (H.uN N t) k) =
          (heatFactor ν t k) • (extendByZero (H.uN N 0) k)
            + (duhamelKernelIntegral ν (F_N N) t) k := by
    intro N t _ht k
    simpa [F_N] using
      (galerkin_duhamelKernel_identity (N := N) (ν := ν) (B := Bop N) (u := H.uN N) (k := k) (t := t)
        (hu := fun s => hu N s) (hint := hint N t k))
  -- Reduce to the forcing-level kernel-integral constructor.
  refine
    nsDuhamelCoeffBound_kernelIntegral_of_forcing (HC := HC) (ν := ν) hν (F_N := F_N) (F := F) ?_ hId'
  intro t ht k
  simpa [F_N] using hF t ht k

/-- Same as `nsDuhamelCoeffBound_galerkinKernel_of_forcing`, but takes the more concrete hypothesis
`GalerkinForcingDominatedConvergenceHypothesis` for the Galerkin forcing modes. -/
def nsDuhamelCoeffBound_galerkinKernel_of_forcingHyp {H : UniformBoundsHypothesis} (HC : ConvergenceHypothesis H)
    (ν : ℝ) (hν : 0 ≤ ν)
    (Bop : (N : ℕ) → ConvectionOp N)
    (hu :
      ∀ N : ℕ, ∀ s : ℝ,
        HasDerivAt (H.uN N) (galerkinNSRHS (N := N) ν (Bop N) (H.uN N s)) s)
    (hint :
      ∀ N : ℕ, ∀ t : ℝ, ∀ k : Mode2,
        IntervalIntegrable (fun s : ℝ =>
          (Real.exp (-(ν * (-kSq k)) * s)) • (extendByZero ((Bop N) (H.uN N s) (H.uN N s)) k))
          MeasureTheory.volume 0 t)
    (hForce : GalerkinForcingDominatedConvergenceHypothesis H Bop) :
    IdentificationHypothesis HC := by
  refine
    nsDuhamelCoeffBound_galerkinKernel_of_forcing (HC := HC) (ν := ν) hν (Bop := Bop) (hu := hu) (hint := hint)
      (F := hForce.F) ?_
  intro t ht k
  -- unpack the forcing-level DCT hypothesis for the Galerkin forcing modes
  simpa [galerkinForcing] using (GalerkinForcingDominatedConvergenceHypothesis.forcingDCTAt (hF := hForce) t ht k)

end IdentificationHypothesis

/-!
## The milestone theorem: “uniform bounds + convergence + identification ⇒ continuum solution”

At this stage the theorem returns the packaged limit object together with its claimed properties.
-/

theorem continuum_limit_exists
    (H : UniformBoundsHypothesis)
    (HC : ConvergenceHypothesis H)
    (HI : IdentificationHypothesis HC) :
    ∃ u : ℝ → FourierState2D,
      (∀ t : ℝ, ∀ k : Mode2, Tendsto (fun N : ℕ => (extendByZero (H.uN N t)) k) atTop (𝓝 ((u t) k)))
        ∧ HI.IsSolution u
        ∧ (∀ t ≥ 0, ∀ k : Mode2, ‖(u t) k‖ ≤ H.B) := by
  refine ⟨HC.u, HC.converges, ?_, ?_⟩
  · simpa using HI.isSolution
  · intro t ht k
    simpa using (ConvergenceHypothesis.coeff_bound_of_uniformBounds (HC := HC) t ht k)

end ContinuumLimit2D

end IndisputableMonolith.ClassicalBridge.Fluids
