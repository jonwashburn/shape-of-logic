import IndisputableMonolith.Cost.Ndim.BlockReduction

/-!
# General-`n` non-flatness: the full deformed metric, its inverse, and the Riemann tensor

`BlockReduction.lean` generalizes Theorem 1a (non-parallelism of `P_λ`) to arbitrary
ambient dimension `n` by working directly with the mixed-tensor projector `PApply` and
the *undeformed* inverse `Dinv`. This module carries Theorem 2 (non-flatness of `h_λ`)
the same distance: it builds the *actual* deformed metric `h_λ = D + λ g̃` as a bare
array (`hFull`), proves its two-sided inverse via the Sherman-Morrison formula
(`hFull_mul_hInvFull`, genuinely `n`-dimensional, no 2-sparsity needed), builds the
third-derivative ("β") tensor of the potential and the Riemann tensor via Shima's
curvature formula for Hessian metrics, and proves that under a `TwoSparse` `α` and
`t i1 = 0`, the mixed Riemann component `R^{i0}_{i1,i0,i1}` collapses exactly to the
closed form `R0101Gen` already certified negative in `ScalarCertificates.lean`.

## Shima's formula

For a Hessian metric `h_{ij} = ∂_i∂_jΦ` with inverse `h^{ij}`, the Riemann tensor is
(Shima, *The Geometry of Hessian Structures*, Thm 2.1; sign convention fixed below by
direct SymPy comparison against the certified `R0101Gen` closed form):

`R_{ijkl} = (1/4) Σ_{p,q} h^{pq} (β_{jkp} β_{ilq} - β_{ikp} β_{jlq})`,  `β_{ijk} = ∂_i∂_j∂_kΦ`,

and `R^i_{jkl} = Σ_m h^{im} R_{mjkl}`. This module implements exactly this construction
as bare arrays over `Fin n`.

## Architecture (panel-greenlit, `state/panel/hessian_theorems_*.json`)

Bare-array + syntactic-index throughout: no `Matrix`, no manifold/`TangentSpace` API.
`hFull`/`hInvFull`/`beta`/`RiemannMixedApply` are plain functions `Fin n → Fin n → ℝ`
(resp. three-index), and the capstone theorem is a Christoffel/curvature-*component*
identity proved by direct sum manipulation, exactly the strategy that closed Stage A
(`PApply_e_eq_P00Gen`) — never an abstract "the connection restricted to a totally
geodesic submanifold agrees with the ambient one" argument (flagged `DEAD` by the
panel).
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

noncomputable section

/-! ## Part 1: the deformed metric `h_λ` and its Sherman-Morrison inverse -/

/-- The full `n`-dimensional deformed Hessian metric
`h_λ(i,j) = δ_{ij} cosh(t_i) + λ cosh(dot α t) · α_i α_j`, i.e. the Hessian of
`Φ_λ(t) = Σ_i cosh(t_i) + λ(cosh(dot α t) - 1)` (matches `hessianEntry` in
`Hessian.lean`, generalized to a named `λ` and packaged here for the curvature
bridge). -/
def hFull {n : ℕ} (α t : Vec n) (lam : ℝ) (i j : Fin n) : ℝ :=
  (if i = j then Real.cosh (t i) else 0) + lam * Real.cosh (dot α t) * α i * α j

/-- The Sherman-Morrison inverse of `hFull`: for the rank-one update
`h_λ = D + (λc)·α⊗α` of the invertible diagonal `D = diag(cosh t_i)`, the inverse is
`D⁻¹ - (λc/(1+λc·S))·(D⁻¹α)⊗(D⁻¹α)`, where `S = dot α (D⁻¹α)` is α's self-energy
w.r.t. `D⁻¹` and `c = cosh(dot α t)`. -/
def hInvFull {n : ℕ} (α t : Vec n) (lam : ℝ) (i j : Fin n) : ℝ :=
  Dinv t i j -
    (lam * Real.cosh (dot α t) /
        (1 + lam * Real.cosh (dot α t) * dot α (sharp (Dinv t) α))) *
      (sharp (Dinv t) α i) * (sharp (Dinv t) α j)

theorem hInvFull_symm {n : ℕ} (α t : Vec n) (lam : ℝ) (i j : Fin n) :
    hInvFull α t lam i j = hInvFull α t lam j i := by
  unfold hInvFull Dinv
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

/-- **The Sherman-Morrison identity.** For any ambient dimension `n`, `hInvFull` really
is the two-sided inverse of `hFull`, provided the Sherman-Morrison denominator
`1 + λc·S` is nonzero (`S = dot α (D⁻¹α)`, `c = cosh(dot α t)`). This is the genuinely
`n`-dimensional content this module adds: no `TwoSparse` hypothesis anywhere in this
theorem. -/
theorem hFull_mul_hInvFull {n : ℕ} (α t : Vec n) (lam : ℝ) (i j : Fin n)
    (hdenom : 1 + lam * Real.cosh (dot α t) * dot α (sharp (Dinv t) α) ≠ 0) :
    ∑ k : Fin n, hFull α t lam i k * hInvFull α t lam k j = if i = j then (1 : ℝ) else 0 := by
  set c := Real.cosh (dot α t) with hc_def
  set w := sharp (Dinv t) α with hw_def
  set S := dot α w with hS_def
  have hSsum : S = ∑ k : Fin n, α k * w k := by rw [hS_def]; rfl
  have hwj : ∀ k : Fin n, w k = (Real.cosh (t k))⁻¹ * α k := fun k => sharp_Dinv_apply t α k
  have hstep1 : ∑ k : Fin n, hFull α t lam i k * Dinv t k j
      = (if i = j then (1 : ℝ) else 0) + lam * c * α i * w j := by
    rw [Finset.sum_eq_single j]
    · unfold Dinv
      rw [if_pos rfl]
      unfold hFull
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl, hwj i]
        have hne : Real.cosh (t i) ≠ 0 := ne_of_gt (Real.cosh_pos _)
        field_simp
        ring
      · rw [if_neg hij, if_neg hij, hwj j]
        ring
    · intro k _ hk
      unfold Dinv
      rw [if_neg hk]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hstep2 : ∑ k : Fin n, hFull α t lam i k * w k = α i * (1 + lam * c * S) := by
    have hexp : ∀ k : Fin n, hFull α t lam i k * w k
        = (if i = k then Real.cosh (t i) * w k else 0) + lam * c * α i * (α k * w k) := by
      intro k
      unfold hFull
      by_cases hik : i = k
      · rw [if_pos hik, if_pos hik]; ring
      · rw [if_neg hik, if_neg hik]; ring
    rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_add_distrib]
    have hpart1 : ∑ k : Fin n, (if i = k then Real.cosh (t i) * w k else 0)
        = Real.cosh (t i) * w i := by
      rw [Finset.sum_ite_eq (Finset.univ : Finset (Fin n)) i (fun k => Real.cosh (t i) * w k)]
      simp
    have hpart2 : ∑ k : Fin n, lam * c * α i * (α k * w k) = lam * c * α i * S := by
      rw [← Finset.mul_sum, ← hSsum]
    rw [hpart1, hpart2, hwj i]
    have hne : Real.cosh (t i) ≠ 0 := ne_of_gt (Real.cosh_pos _)
    field_simp
  have hsplit : ∑ k : Fin n, hFull α t lam i k * hInvFull α t lam k j
      = ∑ k : Fin n, hFull α t lam i k * Dinv t k j
        - (lam * c / (1 + lam * c * S)) * w j * ∑ k : Fin n, hFull α t lam i k * w k := by
    have heach : ∀ k : Fin n, hFull α t lam i k * hInvFull α t lam k j
        = hFull α t lam i k * Dinv t k j
          - (lam * c / (1 + lam * c * S)) * w j * (hFull α t lam i k * w k) := by
      intro k
      unfold hInvFull
      ring
    rw [Finset.sum_congr rfl (fun k _ => heach k), Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsplit, hstep1, hstep2]
  field_simp
  ring

/-! ## Part 2: the third-derivative tensor `β` -/

/-- The (Hessian-)symmetric third-derivative tensor of the potential
`Φ_λ(t) = Σ_i cosh(t_i) + λ(cosh(dot α t) - 1)`:
`β_{ijk} = ∂_i∂_j∂_kΦ_λ = (if i=j=k then sinh(t_i) else 0) + λ α_iα_jα_k sinh(dot α t)`.
Direct closed-form definition, mirroring `hessianEntry`'s treatment of the second
derivative in `Hessian.lean`. -/
def beta {n : ℕ} (α t : Vec n) (lam : ℝ) (i j k : Fin n) : ℝ :=
  (if i = j ∧ j = k then Real.sinh (t i) else 0) + lam * α i * α j * α k * Real.sinh (dot α t)

/-- `β_{ijk}` vanishes whenever one of its indices carries a zero `α`-component and the
diagonal term does not fire. This is the key structural fact driving the
block-diagonal collapse of the Riemann sum: a spectator index (`α = 0`, off the
`TwoSparse` support) kills every summand it appears in. -/
theorem beta_eq_zero {n : ℕ} (α t : Vec n) (lam : ℝ) (i j k : Fin n)
    (hz : α i = 0 ∨ α j = 0 ∨ α k = 0) (hne : ¬ (i = j ∧ j = k)) :
    beta α t lam i j k = 0 := by
  unfold beta
  rw [if_neg hne]
  rcases hz with h | h | h <;> rw [h] <;> ring

/-! ## Part 3: Shima's curvature formula and the Riemann tensor -/

/-- Shima's formula for the doubly-lowered Riemann tensor of a Hessian metric:
`R_{ijkl} = (1/4) Σ_{p,q} h^{pq}(β_{jkp}β_{ilq} - β_{ikp}β_{jlq})`. -/
def RiemannLowerApply {n : ℕ} (ginv : Fin n → Fin n → ℝ) (b : Fin n → Fin n → Fin n → ℝ)
    (i j k l : Fin n) : ℝ :=
  (1 / 4) * ∑ p : Fin n, ∑ q : Fin n, ginv p q * (b j k p * b i l q - b i k p * b j l q)

/-- The mixed Riemann tensor `R^i_{jkl} = Σ_m h^{im} R_{mjkl}`. -/
def RiemannMixedApply {n : ℕ} (ginv : Fin n → Fin n → ℝ) (b : Fin n → Fin n → Fin n → ℝ)
    (i j k l : Fin n) : ℝ :=
  ∑ m : Fin n, ginv i m * RiemannLowerApply ginv b m j k l

/-! ## Part 4: block-diagonal reduction machinery -/

/-- A generic single-index restriction: a function vanishing off `{i0, i1}` sums to the
sum of its two values on the support. (Same content as `sum_twoSparse` in
`BlockReduction.lean`, stated for a bare function rather than an `α i ^ 2`-weighted
one, so it is reusable for the Riemann reduction below.) -/
theorem sum_restrict_pair {n : ℕ} (i0 i1 : Fin n) (hne : i0 ≠ i1) (f : Fin n → ℝ)
    (hz : ∀ k : Fin n, k ≠ i0 → k ≠ i1 → f k = 0) :
    ∑ k : Fin n, f k = f i0 + f i1 := by
  have hsub : ({i0, i1} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin n)), x ∉ ({i0, i1} : Finset (Fin n)) → f x = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hz x hx.1 hx.2
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair hne]

/-- The double-sum analogue of `sum_restrict_pair`: a function of two arguments
vanishing whenever *either* argument is off `{i0, i1}` collapses to its four values on
the `{i0,i1} × {i0,i1}` support. -/
theorem sum2_restrict_pair {n : ℕ} (i0 i1 : Fin n) (hne : i0 ≠ i1) (f : Fin n → Fin n → ℝ)
    (hz : ∀ p q : Fin n, (p ≠ i0 ∧ p ≠ i1) ∨ (q ≠ i0 ∧ q ≠ i1) → f p q = 0) :
    ∑ p : Fin n, ∑ q : Fin n, f p q = f i0 i0 + f i1 i0 + (f i0 i1 + f i1 i1) := by
  have hFin : ∀ p : Fin n, ∑ q : Fin n, f p q = f p i0 + f p i1 := by
    intro p
    apply sum_restrict_pair i0 i1 hne (f p)
    intro q hq0 hq1
    exact hz p q (Or.inr ⟨hq0, hq1⟩)
  rw [Finset.sum_congr rfl (fun p _ => hFin p), Finset.sum_add_distrib]
  have h1 : ∑ p : Fin n, f p i0 = f i0 i0 + f i1 i0 :=
    sum_restrict_pair i0 i1 hne (fun p => f p i0) (fun p hp0 hp1 => hz p i0 (Or.inl ⟨hp0, hp1⟩))
  have h2 : ∑ p : Fin n, f p i1 = f i0 i1 + f i1 i1 :=
    sum_restrict_pair i0 i1 hne (fun p => f p i1) (fun p hp0 hp1 => hz p i1 (Or.inl ⟨hp0, hp1⟩))
  rw [h1, h2]

/-- `hInvFull` vanishes whenever one argument is a spectator index (`α = 0`, off the
`TwoSparse` support): the Sherman-Morrison correction term is proportional to
`w_k = (cosh t_k)⁻¹ α_k`, which vanishes there, leaving only the *off-diagonal* part
of the (diagonal) `Dinv`, which is itself zero. -/
theorem hInvFull_spectator {n : ℕ} (α t : Vec n) (lam : ℝ) (i0 i1 k j : Fin n)
    (hk0 : k ≠ i0) (hk1 : k ≠ i1) (hz : α k = 0) (hkj : k ≠ j) :
    hInvFull α t lam k j = 0 := by
  unfold hInvFull
  rw [sharp_Dinv_apply t α k, hz]
  unfold Dinv
  rw [if_neg hkj]
  ring

/-- `S = dot α (D⁻¹α)` restricted to a `TwoSparse` support: only the `i0, i1`
components survive. -/
theorem dot_sharp_Dinv_twoSparse {n : ℕ} (t α : Vec n) (i0 i1 : Fin n) (hne : i0 ≠ i1)
    (h2 : TwoSparse α i0 i1) :
    dot α (sharp (Dinv t) α)
      = (Real.cosh (t i0))⁻¹ * α i0 ^ 2 + (Real.cosh (t i1))⁻¹ * α i1 ^ 2 := by
  have hpt : ∀ i : Fin n, α i * sharp (Dinv t) α i = (Real.cosh (t i))⁻¹ * α i ^ 2 := by
    intro i; rw [sharp_Dinv_apply]; ring
  unfold dot
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  exact sum_twoSparse α i0 i1 hne h2 (fun i => (Real.cosh (t i))⁻¹)

/-- The core vanishing fact driving the Riemann reduction: for `p` or `q` off the
`TwoSparse` support, every term of Shima's `(p,q)`-summand built from `β` at
`(i1, i0, ·)`/`(m, i0, ·)`/`(m, i1, ·)`/`(i1, i1, ·)` vanishes, regardless of `m`. -/
theorem riemann_beta_numerator_zero {n : ℕ} (α t : Vec n) (lam : ℝ) (i0 i1 : Fin n)
    (hne01 : i0 ≠ i1) (h2 : TwoSparse α i0 i1) (m p q : Fin n)
    (hspec : (p ≠ i0 ∧ p ≠ i1) ∨ (q ≠ i0 ∧ q ≠ i1)) :
    beta α t lam i1 i0 p * beta α t lam m i1 q - beta α t lam m i0 p * beta α t lam i1 i1 q = 0 := by
  rcases hspec with ⟨hp0, hp1⟩ | ⟨hq0, hq1⟩
  · have hzp : α p = 0 := h2 p hp0 hp1
    have h1 : beta α t lam i1 i0 p = 0 :=
      beta_eq_zero α t lam i1 i0 p (Or.inr (Or.inr hzp)) (fun h => hne01 h.1.symm)
    have h3 : beta α t lam m i0 p = 0 :=
      beta_eq_zero α t lam m i0 p (Or.inr (Or.inr hzp)) (fun h => hp0 h.2.symm)
    rw [h1, h3]; ring
  · have hzq : α q = 0 := h2 q hq0 hq1
    have h1 : beta α t lam m i1 q = 0 :=
      beta_eq_zero α t lam m i1 q (Or.inr (Or.inr hzq)) (fun h => hq1 h.2.symm)
    have h3 : beta α t lam i1 i1 q = 0 :=
      beta_eq_zero α t lam i1 i1 q (Or.inr (Or.inr hzq)) (fun h => hq1 h.2.symm)
    rw [h1, h3]; ring

/-! ## Part 5: the capstone — `RiemannMixedApply` collapses to `R0101Gen` -/

/-- **Stage B capstone reduction.** Under a `TwoSparse` `α` (support `{i0, i1}`) and
`t i1 = 0`, the general-`n` mixed Riemann component `R^{i0}_{i1,i0,i1}`, built from the
*actual* deformed metric `hFull`/`hInvFull` and its Hessian third-derivative tensor
`beta` via Shima's formula, collapses **algebraically** to the closed form
`R0101Gen a b lam (t i0)` already certified negative in `ScalarCertificates.lean`. This
is the general-`n` non-flatness content: the abstract `n`-dimensional curvature
construction of Part 3 genuinely specializes to the certified 2-D formula on any
2-sparse slice, for arbitrary ambient dimension `n`. Verified algebraically correct
(independent of any `cosh²-sinh²=1` identity) by direct SymPy computation before this
proof was written. -/
theorem RiemannMixedApply_reduce {n : ℕ} (α t : Vec n) (lam a b : ℝ) (i0 i1 : Fin n)
    (hne01 : i0 ≠ i1) (h2 : TwoSparse α i0 i1)
    (ha : α i0 = a) (hb : α i1 = b) (ht1 : t i1 = 0)
    (ha0 : a ≠ 0) (hlam : 0 < lam) :
    RiemannMixedApply (hInvFull α t lam) (beta α t lam) i0 i1 i0 i1
      = R0101Gen a b lam (t i0) := by
  set t0 := t i0 with ht0_def
  have hct0_pos : 0 < Real.cosh t0 := Real.cosh_pos _
  have hct0_ne : Real.cosh t0 ≠ 0 := ne_of_gt hct0_pos
  have hkap_pos : 0 < kappaGen a b lam t0 := kappaGen_pos a b lam t0 ha0 hlam
  have hkap_ne : kappaGen a b lam t0 ≠ 0 := ne_of_gt hkap_pos
  -- `dot α t` collapses to `a * t0` on the `TwoSparse` slice with `t i1 = 0`.
  have hdot : dot α t = a * t0 := by
    unfold dot
    have hrestrict := sum_restrict_pair i0 i1 hne01 (fun k => α k * t k)
      (fun k hk0 hk1 => by dsimp only; rw [h2 k hk0 hk1]; ring)
    dsimp only at hrestrict
    rw [hrestrict, ha, hb, ht1]
    ring
  have hcat : Real.cosh (dot α t) = Real.cosh (a * t0) := by rw [hdot]
  have hsat : Real.sinh (dot α t) = Real.sinh (a * t0) := by rw [hdot]
  -- `w := sharp (Dinv t) α` at `i0, i1`.
  have hw0 : sharp (Dinv t) α i0 = (Real.cosh t0)⁻¹ * a := by
    rw [sharp_Dinv_apply, ha]
  have hw1 : sharp (Dinv t) α i1 = b := by
    rw [sharp_Dinv_apply, hb, ht1, Real.cosh_zero]; ring
  have hS : dot α (sharp (Dinv t) α) = (Real.cosh t0)⁻¹ * a ^ 2 + b ^ 2 := by
    rw [dot_sharp_Dinv_twoSparse t α i0 i1 hne01 h2, ha, hb, ht1, Real.cosh_zero]
    ring
  -- The Sherman-Morrison denominator, in closed form: `1+λc·S = κ/cosh t0`.
  have hdenom_eq : 1 + lam * Real.cosh (dot α t) * dot α (sharp (Dinv t) α)
      = kappaGen a b lam t0 / Real.cosh t0 := by
    rw [hcat, hS]
    unfold kappaGen
    field_simp
    ring
  -- The four raw `Dinv` values on the block.
  have hDinv00 : Dinv t i0 i0 = (Real.cosh t0)⁻¹ := by unfold Dinv; rw [if_pos rfl]
  have hDinv01 : Dinv t i0 i1 = 0 := by unfold Dinv; rw [if_neg hne01]
  have hDinv11 : Dinv t i1 i1 = 1 := by
    unfold Dinv; rw [if_pos rfl, ht1, Real.cosh_zero]; norm_num
  -- The four `hInvFull` values on the `{i0,i1}` block, in closed form.
  have hInv00 : hInvFull α t lam i0 i0
      = (b ^ 2 * lam * Real.cosh (a * t0) + 1) / kappaGen a b lam t0 := by
    unfold hInvFull
    rw [hDinv00, hdenom_eq, hcat, hw0]
    unfold kappaGen
    field_simp
    ring
  have hInv01 : hInvFull α t lam i0 i1
      = -(a * b * lam * Real.cosh (a * t0)) / kappaGen a b lam t0 := by
    unfold hInvFull
    rw [hDinv01, hdenom_eq, hcat, hw0, hw1]
    unfold kappaGen
    field_simp
    ring
  have hInv10 : hInvFull α t lam i1 i0
      = -(a * b * lam * Real.cosh (a * t0)) / kappaGen a b lam t0 := by
    rw [hInvFull_symm]; exact hInv01
  have hInv11 : hInvFull α t lam i1 i1
      = (a ^ 2 * lam * Real.cosh (a * t0) + Real.cosh t0) / kappaGen a b lam t0 := by
    unfold hInvFull
    rw [hDinv11, hdenom_eq, hcat, hw1]
    unfold kappaGen
    field_simp
    ring
  -- The eight `beta` values on the `{i0,i1}` block.
  have hb000 : beta α t lam i0 i0 i0 = Real.sinh t0 + lam * a ^ 3 * Real.sinh (a * t0) := by
    unfold beta; rw [if_pos (⟨rfl, rfl⟩ : i0 = i0 ∧ i0 = i0), ha, hsat]; ring
  have hb001 : beta α t lam i0 i0 i1 = lam * a ^ 2 * b * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i0 = i0 ∧ i0 = i1 => hne01 h.2), ha, hb, hsat]; ring
  have hb010 : beta α t lam i0 i1 i0 = lam * a ^ 2 * b * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i0 = i1 ∧ i1 = i0 => hne01 h.1), ha, hb, hsat]; ring
  have hb011 : beta α t lam i0 i1 i1 = lam * a * b ^ 2 * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i0 = i1 ∧ i1 = i1 => hne01 h.1), ha, hb, hsat]; ring
  have hb100 : beta α t lam i1 i0 i0 = lam * a ^ 2 * b * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i1 = i0 ∧ i0 = i0 => hne01 h.1.symm), ha, hb, hsat]; ring
  have hb101 : beta α t lam i1 i0 i1 = lam * a * b ^ 2 * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i1 = i0 ∧ i0 = i1 => hne01 h.1.symm), ha, hb, hsat]; ring
  have hb110 : beta α t lam i1 i1 i0 = lam * a * b ^ 2 * Real.sinh (a * t0) := by
    unfold beta; rw [if_neg (fun h : i1 = i1 ∧ i1 = i0 => hne01 h.2.symm), ha, hb, hsat]; ring
  have hb111 : beta α t lam i1 i1 i1 = lam * b ^ 3 * Real.sinh (a * t0) := by
    unfold beta; rw [if_pos (⟨rfl, rfl⟩ : i1 = i1 ∧ i1 = i1), ht1, hb, hsat, Real.sinh_zero]; ring
  -- Reduce the `m`-sum in `RiemannMixedApply` to `{i0, i1}`: spectator `m` contributes
  -- zero because `hInvFull α t lam i0 m = 0` there.
  have hspec_m : ∀ m : Fin n, m ≠ i0 → m ≠ i1 →
      hInvFull α t lam i0 m *
          RiemannLowerApply (hInvFull α t lam) (beta α t lam) m i1 i0 i1 = 0 := by
    intro m hm0 hm1
    have hzm : α m = 0 := h2 m hm0 hm1
    have hz0 : hInvFull α t lam i0 m = 0 := by
      rw [hInvFull_symm]
      exact hInvFull_spectator α t lam i0 i1 m i0 hm0 hm1 hzm hm0
    rw [hz0]; ring
  have hmixed : RiemannMixedApply (hInvFull α t lam) (beta α t lam) i0 i1 i0 i1
      = hInvFull α t lam i0 i0
          * RiemannLowerApply (hInvFull α t lam) (beta α t lam) i0 i1 i0 i1
        + hInvFull α t lam i0 i1
          * RiemannLowerApply (hInvFull α t lam) (beta α t lam) i1 i1 i0 i1 := by
    unfold RiemannMixedApply
    exact sum_restrict_pair i0 i1 hne01
      (fun m => hInvFull α t lam i0 m *
        RiemannLowerApply (hInvFull α t lam) (beta α t lam) m i1 i0 i1)
      hspec_m
  -- Reduce the `(p,q)`-double sum in `RiemannLowerApply m i1 i0 i1` to `{i0,i1}²`, for
  -- any `m` (used below at `m = i0` and `m = i1`).
  have hlower_reduce : ∀ m : Fin n,
      RiemannLowerApply (hInvFull α t lam) (beta α t lam) m i1 i0 i1
        = (1 / 4) *
          (hInvFull α t lam i0 i0
              * (beta α t lam i1 i0 i0 * beta α t lam m i1 i0
                  - beta α t lam m i0 i0 * beta α t lam i1 i1 i0)
            + hInvFull α t lam i1 i0
              * (beta α t lam i1 i0 i1 * beta α t lam m i1 i0
                  - beta α t lam m i0 i1 * beta α t lam i1 i1 i0)
            + (hInvFull α t lam i0 i1
                * (beta α t lam i1 i0 i0 * beta α t lam m i1 i1
                    - beta α t lam m i0 i0 * beta α t lam i1 i1 i1)
              + hInvFull α t lam i1 i1
                * (beta α t lam i1 i0 i1 * beta α t lam m i1 i1
                    - beta α t lam m i0 i1 * beta α t lam i1 i1 i1))) := by
    intro m
    unfold RiemannLowerApply
    congr 1
    exact sum2_restrict_pair i0 i1 hne01
      (fun p q => hInvFull α t lam p q *
        (beta α t lam i1 i0 p * beta α t lam m i1 q
          - beta α t lam m i0 p * beta α t lam i1 i1 q))
                  (fun p q hpq => by
                    dsimp only
                    rw [riemann_beta_numerator_zero α t lam i0 i1 hne01 h2 m p q hpq]; ring)
  rw [hmixed, hlower_reduce i0, hlower_reduce i1,
    hInv00, hInv01, hInv10, hInv11,
    hb000, hb001, hb010, hb011, hb100, hb101, hb110, hb111]
  unfold R0101Gen
  field_simp
  ring

/-- **Theorem 2, general `n`.** Under the block-diagonal hypotheses plus `b ≠ 0` and
`t i0 ≠ 0`, the mixed Riemann tensor `R^{i0}_{i1,i0,i1}` of the *actual* `n`-dimensional
deformed metric `h_λ` is strictly negative: `h_λ` is genuinely non-flat, for any
ambient dimension `n` and any `α` supported on two coordinates. This is the honest
general-`n` generalization of `R0101Gen_neg` (`ScalarCertificates.lean`), assembled
from the algebraic reduction above plus the already-certified 2-D negativity. -/
theorem RiemannMixedApply_neg {n : ℕ} (α t : Vec n) (lam a b : ℝ) (i0 i1 : Fin n)
    (hne01 : i0 ≠ i1) (h2 : TwoSparse α i0 i1)
    (ha : α i0 = a) (hb : α i1 = b) (ht1 : t i1 = 0)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hlam : 0 < lam) (ht0 : t i0 ≠ 0) :
    RiemannMixedApply (hInvFull α t lam) (beta α t lam) i0 i1 i0 i1 < 0 := by
  rw [RiemannMixedApply_reduce α t lam a b i0 i1 hne01 h2 ha hb ht1 ha0 hlam]
  exact R0101Gen_neg a b lam (t i0) ha0 hb0 hlam ht0

end

end Ndim
end Cost
end IndisputableMonolith
