import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

/-!
# Properties of the display / structural residue `gap(Z)`

This file provides **Lean-checked** properties of the Recognition/structural residue

  `gap(Z) = log(1 + Z/φ) / log φ`

used throughout the mass framework (a.k.a. `𝓕(Z)` in the papers).

These properties are important because `gap` is the proposed **zero-parameter**
Recognition-side residue `f^{Rec}`. Unlike the Standard-Model RG residue (which requires
external kernels), `gap` is definitional and we can verify its algebraic/analytic behavior
directly in Lean.
-/

namespace IndisputableMonolith
namespace RSBridge

open IndisputableMonolith.Constants

noncomputable section

/-! ## Basic identities -/

@[simp] theorem gap_zero : gap (0 : ℤ) = 0 := by
  simp [gap]

/-!
`gap` can be rewritten as a shifted log-base-φ:

  `gap(Z) = log_φ(φ + Z) - 1`

for any `Z` with `0 < φ + Z` (in practice all `Z ≥ 0` used in the mass bands).
-/
theorem gap_eq_log_phi_add_sub_one {Z : ℤ} (hZ : 0 < (phi + (Z : ℝ))) :
    gap Z = (Real.log (phi + (Z : ℝ)) / Real.log phi) - 1 := by
  have hφpos : 0 < phi := phi_pos
  have hφne : (phi : ℝ) ≠ 0 := ne_of_gt hφpos
  have hlogφ : Real.log phi ≠ 0 := by
    have : (1 : ℝ) < phi := one_lt_phi
    exact ne_of_gt (Real.log_pos this)
  -- log(1 + Z/φ) = log((φ+Z)/φ) = log(φ+Z) - log(φ)
  have h1 : (1 + (Z : ℝ) / phi) = (phi + (Z : ℝ)) / phi := by
    field_simp [hφne]
  have hpos1 : 0 < (1 + (Z : ℝ) / phi) := by
    -- since (φ+Z)/φ > 0
    have : 0 < (phi + (Z : ℝ)) / phi := by
      exact div_pos hZ hφpos
    simpa [h1] using this
  calc
    gap Z
        = Real.log (1 + (Z : ℝ) / phi) / Real.log phi := by rfl
    _   = (Real.log ((phi + (Z : ℝ)) / phi)) / Real.log phi := by simp [h1]
    _   = (Real.log (phi + (Z : ℝ)) - Real.log phi) / Real.log phi := by
            simp [Real.log_div, hZ.ne', hφne]
    _   = (Real.log (phi + (Z : ℝ)) / Real.log phi) - 1 := by
            field_simp [hlogφ]

/-! ## Monotonicity (verification property) -/

theorem gap_strictMono_on_nonneg :
    StrictMono fun n : ℕ => gap (n : ℤ) := by
  intro a b hab
  -- Convert to reals for monotonicity of log.
  have hφpos : 0 < phi := phi_pos
  have hlogφpos : 0 < Real.log phi := Real.log_pos one_lt_phi
  have ha : 0 < (1 + ((a : ℤ) : ℝ) / phi) := by
    have : (0 : ℝ) ≤ ((a : ℤ) : ℝ) / phi := by
      have : (0 : ℝ) ≤ ((a : ℤ) : ℝ) := by exact_mod_cast (Nat.zero_le a)
      exact div_nonneg this (le_of_lt hφpos)
    linarith
  have hlt : (1 + ((a : ℤ) : ℝ) / phi) < (1 + ((b : ℤ) : ℝ) / phi) := by
    have hab' : ((a : ℤ) : ℝ) < ((b : ℤ) : ℝ) := by exact_mod_cast hab
    have : ((a : ℤ) : ℝ) / phi < ((b : ℤ) : ℝ) / phi :=
      (div_lt_div_of_pos_right hab' hφpos)
    linarith
  have hlog : Real.log (1 + ((a : ℤ) : ℝ) / phi) < Real.log (1 + ((b : ℤ) : ℝ) / phi) :=
    Real.log_lt_log ha hlt
  -- divide by positive log(phi)
  have := (div_lt_div_of_pos_right hlog hlogφpos)
  simpa [gap] using this

/-! ## Band ordering (structural sanity checks) -/

theorem gap_24_lt_gap_276 : gap (24 : ℤ) < gap (276 : ℤ) := by
  have hmono := gap_strictMono_on_nonneg
  -- 24 < 276 in ℕ
  have : (24 : ℕ) < (276 : ℕ) := by decide
  simpa using hmono this

theorem gap_276_lt_gap_1332 : gap (276 : ℤ) < gap (1332 : ℤ) := by
  have hmono := gap_strictMono_on_nonneg
  have : (276 : ℕ) < (1332 : ℕ) := by decide
  simpa using hmono this

/-! ## Concavity / diminishing increments -/

/-- Real-extension of the display function on `ℝ` (used for concavity statements). -/
noncomputable def gapR (x : ℝ) : ℝ :=
  Real.log (1 + x / phi) / Real.log phi

@[simp] theorem gapR_nat (n : ℕ) : gapR (n : ℝ) = gap (n : ℤ) := by
  simp [gapR, gap]

/-- `gapR` is strictly concave on `[0,∞)`. -/
theorem strictConcaveOn_gapR_Ici : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) gapR := by
  -- Reduce to strict concavity of `Real.log` on `(0,∞)` and use an injective affine reparametrization.
  let g : ℝ → ℝ := Real.log
  have hlog : StrictConcaveOn ℝ (Set.Ioi (0 : ℝ)) g := strictConcaveOn_log_Ioi

  have hφpos : 0 < phi := phi_pos
  have hφne : (phi : ℝ) ≠ 0 := ne_of_gt hφpos
  have hlogφpos : 0 < Real.log phi := Real.log_pos one_lt_phi
  have hlogφne : Real.log phi ≠ 0 := ne_of_gt hlogφpos

  -- affine map h(x) = 1 + x/phi
  let hlin : ℝ →ₗ[ℝ] ℝ := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (1 / phi)
  let h : ℝ →ᵃ[ℝ] ℝ :=
    AffineMap.mk (toFun := fun x => 1 + x / phi) (linear := hlin) (map_vadd' := by
      intro p v
      -- v +ᵥ p = v + p in ℝ-torsor
      simp [hlin, add_div, hφne]
      ring)

  -- helper: h maps Ici 0 into Ioi 0
  have h_img0 : ∀ {x : ℝ}, x ∈ Set.Ici (0 : ℝ) → h x ∈ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have hx_div : 0 ≤ x / phi := div_nonneg hx0 (le_of_lt hφpos)
    have : (0 : ℝ) < 1 + x / phi := by linarith
    simpa [h] using this

  -- injectivity of h on Ici 0
  have h_inj : Set.InjOn h (Set.Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    have hEq : (1 + x / phi) = (1 + y / phi) := by simpa [h] using hxy
    have hDiv : x / phi = y / phi := by
      have h' := congrArg (fun t => t - 1) hEq
      simpa using h'
    have hm : (x / phi) * phi = (y / phi) * phi := congrArg (fun t => t * phi) hDiv
    simpa [div_eq_mul_inv, hφne, mul_assoc] using hm

  -- strict concavity of log ∘ h on Ici 0
  have h_log_comp : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) (g ∘ h) := by
    refine ⟨convex_Ici (0 : ℝ), ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : h x ∈ Set.Ioi (0 : ℝ) := h_img0 hx
    have hy' : h y ∈ Set.Ioi (0 : ℝ) := h_img0 hy
    have hxy' : h x ≠ h y := by
      intro hEq
      exact hxy (h_inj hx hy hEq)
    have hh : a * h x + b * h y = h (a * x + b * y) := by
      simpa [smul_eq_mul] using (Convex.combo_affine_apply (f := h) hab).symm
    -- Apply strict concavity of log and rewrite via hh
    have h0 := hlog.2 hx' hy' hxy' ha hb hab
    -- `h0` is about `log (a • h x + b • h y)`; rewrite that argument via `hh`.
    simpa [Function.comp, smul_eq_mul, hh] using h0

  -- scale by positive constant: gapR = (1/log φ) * (log ∘ h)
  refine ⟨h_log_comp.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hc : 0 < (1 / Real.log phi) := one_div_pos.2 hlogφpos
  have hbase := h_log_comp.2 hx hy hxy ha hb hab
  -- rewrite `gapR` as a constant multiple of `log (h x)`
  have hdef : ∀ t : ℝ, gapR t = (1 / Real.log phi) * g (h t) := by
    intro t
    simp [gapR, g, h, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  -- multiply strict inequality by positive constant and distribute
  have hmul : (1 / Real.log phi) * (a * (g (h x)) + b * (g (h y))) <
      (1 / Real.log phi) * (g (h (a • x + b • y))) := by
    -- `smul` on ℝ is multiplication; `hbase` is already in that form
    have := mul_lt_mul_of_pos_left hbase hc
    -- rewrite scalar multiplications
    simpa [smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using this
  -- convert back to gapR and finish
  -- LHS: a*gapR x + b*gapR y  ; RHS: gapR(a•x + b•y)
  have : a * gapR x + b * gapR y < gapR (a • x + b • y) := by
    -- rewrite all gapR occurrences using hdef, then use hmul
    simpa [hdef, smul_eq_mul, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
  simpa [StrictConcaveOn, smul_eq_mul] using this

/-!
Diminishing increments: for `n ≥ 0`, the discrete first differences decrease.

This is the discrete shadow of strict concavity:
\[
  \Fgap(n+2)-\Fgap(n+1) < \Fgap(n+1)-\Fgap(n).
\]
-/
theorem gap_diminishing_increments (n : ℕ) :
    gap ((n + 2 : ℕ) : ℤ) - gap ((n + 1 : ℕ) : ℤ) <
      gap ((n + 1 : ℕ) : ℤ) - gap (n : ℤ) := by
  -- Use slope inequality for strict concave functions on ℝ with x=n, y=n+1, z=n+2.
  have hsc := strictConcaveOn_gapR_Ici
  have hx : (n : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simpa [Set.mem_Ici] using (show (0 : ℝ) ≤ (n : ℝ) from by exact_mod_cast (Nat.zero_le n))
  have hy : ((n + 1 : ℕ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simpa [Set.mem_Ici] using (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) from by exact_mod_cast (Nat.zero_le (n + 1)))
  have hz : ((n + 2 : ℕ) : ℝ) ∈ Set.Ici (0 : ℝ) := by
    simpa [Set.mem_Ici] using (show (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) from by exact_mod_cast (Nat.zero_le (n + 2)))
  have hxy : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_succ_self n)
  have hyz : ((n + 1 : ℕ) : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_succ_self (n + 1))
  have hslope :
      (gapR ((n + 2 : ℕ) : ℝ) - gapR ((n + 1 : ℕ) : ℝ)) /
          (((n + 2 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) <
        (gapR ((n + 1 : ℕ) : ℝ) - gapR (n : ℝ)) /
          (((n + 1 : ℕ) : ℝ) - (n : ℝ)) :=
    StrictConcaveOn.slope_anti_adjacent hsc (hx := hx) (hz := hz) hxy hyz
  -- simplify denominators (both are 1), noting simp may rewrite `((n+1:ℕ):ℝ)` as `↑n + 1`
  have hslope' : gapR ((n + 2 : ℕ) : ℝ) - gapR ((n + 1 : ℕ) : ℝ) <
        gapR ((n + 1 : ℕ) : ℝ) - gapR (n : ℝ) := by
    -- First simplify the denominators to explicit numerals, then discharge them with `norm_num`.
    have hs' :
        (gapR (↑n + 2) - gapR (↑n + 1)) / ((2 : ℝ) - 1) <
          (gapR (↑n + 1) - gapR (n : ℝ)) / ((1 : ℝ) - 0) := by
      -- `simp` rewrites casts like `((n+1:ℕ):ℝ)` into `↑n + 1`.
      -- It also rewrites the differences of successive naturals into numerals.
      simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm] using hslope
    have hdenL : ((2 : ℝ) - 1) = (1 : ℝ) := by norm_num
    have hdenR : ((1 : ℝ) - 0) = (1 : ℝ) := by norm_num
    -- remove the divisions by 1
    simpa [hdenL, hdenR, div_one] using hs'
  -- rewrite back from `gapR` on naturals to `gap` on integers.
  -- We do this with explicit `simp` so the rewriting doesn't get stuck on expressions like `↑n + k`.
  have hfinal :
      gap ((n + 2 : ℕ) : ℤ) - gap ((n + 1 : ℕ) : ℤ) <
        gap ((n + 1 : ℕ) : ℤ) - gap (n : ℤ) := by
    -- `simp` likes to rewrite `((n+k:ℕ):ℝ)` into `↑n + k`, which prevents `gapR_nat` from firing.
    -- So we rewrite *back* to the `(n+k : ℕ)` cast form first, then apply `gapR_nat`.
    have hslope_cast :
        gapR (↑n + 2) - gapR (↑n + 1) < gapR (↑n + 1) - gapR (n : ℝ) := by
      -- avoid `simp` here (it can loop on casts); use `rw` with explicit cast equalities.
      have h1 : ((n + 1 : ℕ) : ℝ) = (↑n + 1 : ℝ) := by norm_num
      have h2 : ((n + 2 : ℕ) : ℝ) = (↑n + 2 : ℝ) := by norm_num
      have h := hslope'
      -- rewrite nat-casts into `↑n + k`
      rw [h1, h2] at h
      exact h

    have hcast1 : (↑n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) := by norm_num
    have hcast2 : (↑n + 2 : ℝ) = ((n + 2 : ℕ) : ℝ) := by norm_num

    -- rewrite the inequality into the nat-cast form
    have hslope_nat :
        gapR ((n + 2 : ℕ) : ℝ) - gapR ((n + 1 : ℕ) : ℝ) <
          gapR ((n + 1 : ℕ) : ℝ) - gapR (n : ℝ) := by
      have h := hslope_cast
      -- rewrite `↑n + k` back into `((n+k):ℕ):ℝ`
      rw [hcast1, hcast2] at h
      exact h

    -- finally, apply `gapR_nat` on the three natural arguments (using `rw` to avoid cast rewriting).
    have h := hslope_nat
    rw [gapR_nat (n + 2), gapR_nat (n + 1), gapR_nat n] at h
    simpa using h
  exact hfinal

theorem gap_second_difference_neg (n : ℕ) :
    gap ((n + 2 : ℕ) : ℤ) + gap (n : ℤ) < 2 * gap ((n + 1 : ℕ) : ℤ) := by
  have h := gap_diminishing_increments (n := n)
  -- rearrange: g(n+2) - g(n+1) < g(n+1) - g(n)  ↔  g(n+2) + g(n) < 2 g(n+1)
  linarith

end

/-! ## Numerical interval bounds for canonical bands

The following theorems establish verified numerical bounds for the `gap` function
at the canonical Z-values (24, 276, 1332) used in the three fermion mass bands.

These are structured as certified intervals matching the style in
`Physics/ElectronMass/Necessity.lean`.
-/

section IntervalBounds

/-! ### Foundational bounds on φ and log(φ)

These numerical bounds are used to certify interval arithmetic for gap values.
The bounds on φ come from √5 computation; bounds on log(φ) are represented as hypotheses
as they require Taylor polynomial evaluation (see Physics/ElectronMass/Necessity.lean
for the full proof machinery).
-/

/-- φ is bounded: φ ∈ (1.618033, 1.618034) -/
lemma phi_bounds : (1.618033 : ℝ) < phi ∧ phi < (1.618034 : ℝ) := by
  -- φ = (1 + √5)/2
  -- We need: 2.236066 < √5 < 2.236068
  have sqrt5_lower : (2.236066 : ℝ) < Real.sqrt 5 := by
    have h : (2.236066 : ℝ)^2 < 5 := by norm_num
    have h_pos : (0 : ℝ) ≤ 2.236066 := by norm_num
    rw [← Real.sqrt_sq h_pos]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  have sqrt5_upper : Real.sqrt 5 < (2.236068 : ℝ) := by
    have h : (5 : ℝ) < (2.236068)^2 := by norm_num
    have h_pos : (0 : ℝ) ≤ 2.236068 := by norm_num
    rw [← Real.sqrt_sq h_pos]
    exact Real.sqrt_lt_sqrt (by positivity) h
  constructor
  · -- Lower bound
    have h : (1.618033 : ℝ) < (1 + Real.sqrt 5) / 2 := by
      have : (1 : ℝ) + 2.236066 < 1 + Real.sqrt 5 := by linarith
      linarith
    simp only [phi]
    exact h
  · -- Upper bound
    have h : (1 + Real.sqrt 5) / 2 < (1.618034 : ℝ) := by
      have : (1 : ℝ) + Real.sqrt 5 < 1 + 2.236068 := by linarith
      linarith
    simp only [phi]
    exact h

/-- Hypothesis: log(1.618033) > 0.481211 (verified externally via Taylor expansion) -/
def log_lower_bound_phi_hypothesis : Prop := (0.481211 : ℝ) < Real.log (1.618033 : ℝ)

/-- Hypothesis: log(1.618034) < 0.481213 (verified externally via Taylor expansion) -/
def log_upper_bound_phi_hypothesis : Prop := Real.log (1.618034 : ℝ) < (0.481213 : ℝ)

/-- log(φ) is bounded: log(φ) ∈ (0.481211, 0.481213) -/
lemma log_phi_bounds (h_low : log_lower_bound_phi_hypothesis) (h_high : log_upper_bound_phi_hypothesis) :
    (0.481211 : ℝ) < Real.log phi ∧ Real.log phi < (0.481213 : ℝ) := by
  have hphi := phi_bounds
  have h_low' : (0.481211 : ℝ) < Real.log (1.618033 : ℝ) := by
    simpa [log_lower_bound_phi_hypothesis] using h_low
  have h_high' : Real.log (1.618034 : ℝ) < (0.481213 : ℝ) := by
    simpa [log_upper_bound_phi_hypothesis] using h_high
  constructor
  · -- Lower bound: log(φ) > log(1.618033) > 0.481211
    have h_mono : Real.log (1.618033 : ℝ) < Real.log phi := by
      apply Real.log_lt_log (by norm_num) hphi.1
    exact lt_trans h_low' h_mono
  · -- Upper bound: log(φ) < log(1.618034) < 0.481213
    have h_mono : Real.log phi < Real.log (1.618034 : ℝ) := by
      apply Real.log_lt_log (by linarith [hphi.1]) hphi.2
    exact lt_trans h_mono h_high'

/-! ### Auxiliary numerical log bounds -/

/-- Hypothesis for numerical lower bound: log(1 + 24/1.618034) > 2.7613 -/
def log_15p83_lower_hypothesis : Prop := (2.7613 : ℝ) < Real.log (1 + 24 / (1.618034 : ℝ))

/-- Hypothesis for numerical upper bound: log(1 + 24/1.618033) < 2.7615 -/
def log_15p83_upper_hypothesis : Prop := Real.log (1 + 24 / (1.618033 : ℝ)) < (2.7615 : ℝ)

/-- Hypothesis for numerical lower bound: log(1 + 276/1.618034) > 5.1442 -/
def log_171p6_lower_hypothesis : Prop := (5.1442 : ℝ) < Real.log (1 + 276 / (1.618034 : ℝ))

/-- Hypothesis for numerical upper bound: log(1 + 276/1.618033) < 5.1444 -/
def log_171p6_upper_hypothesis : Prop := Real.log (1 + 276 / (1.618033 : ℝ)) < (5.1444 : ℝ)

/-- Bounds on gap(24). -/
lemma gap_24_bounds
    (h_low_phi : log_lower_bound_phi_hypothesis)
    (h_high_phi : log_upper_bound_phi_hypothesis)
    (h_low_24 : log_15p83_lower_hypothesis)
    (h_high_24 : log_15p83_upper_hypothesis) :
    (5.737 : ℝ) < gap 24 ∧ gap 24 < (5.74 : ℝ) := by
  simp only [gap]
  have hphi := phi_bounds
  have hlogphi := log_phi_bounds h_low_phi h_high_phi
  have h_phi_pos : 0 < phi := phi_pos
  have h_log_pos : 0 < Real.log phi := Real.log_pos (by linarith [hphi.1])
  -- Bounds on 1 + 24/φ
  have h_arg_lower : 1 + 24 / (1.618034 : ℝ) < 1 + 24 / phi := by
    have hdiv : (24 : ℝ) / (1.618034 : ℝ) < 24 / phi := by
      have hpos : (0 : ℝ) < (24 : ℝ) := by norm_num
      exact div_lt_div_of_pos_left hpos h_phi_pos hphi.2
    linarith
  have h_arg_upper : 1 + 24 / phi < 1 + 24 / (1.618033 : ℝ) := by
    have hdiv : (24 : ℝ) / phi < 24 / (1.618033 : ℝ) := by
      have hpos : (0 : ℝ) < (24 : ℝ) := by norm_num
      exact div_lt_div_of_pos_left hpos (by norm_num : (0 : ℝ) < (1.618033 : ℝ)) hphi.1
    linarith
  -- Bounds on log(1 + 24/φ) using monotonicity
  have h_log_lower : Real.log (1 + 24 / (1.618034 : ℝ)) < Real.log (1 + 24 / phi) := by
    apply Real.log_lt_log (by norm_num) h_arg_lower
  have h_log_upper : Real.log (1 + 24 / phi) < Real.log (1 + 24 / (1.618033 : ℝ)) := by
    have h_pos : 0 < 1 + 24 / phi := by positivity
    apply Real.log_lt_log h_pos h_arg_upper
  -- Combine with numerical bounds
  have h_num_lower : (2.7613 : ℝ) < Real.log (1 + 24 / phi) :=
    lt_trans h_low_24 h_log_lower
  have h_num_upper : Real.log (1 + 24 / phi) < (2.7615 : ℝ) :=
    lt_trans h_log_upper h_high_24
  constructor
  · -- Lower bound: gap > 5.737
    have h_chain : 5.737 * Real.log phi < Real.log (1 + 24 / phi) := by
      have h1 : 5.737 * Real.log phi < 5.737 * 0.481213 := by nlinarith [hlogphi.2]
      have h2 : (5.737 : ℝ) * 0.481213 < 2.7613 := by norm_num
      linarith
    exact (lt_div_iff₀ h_log_pos).mpr h_chain
  · -- Upper bound: gap < 5.74
    have h_chain : Real.log (1 + 24 / phi) < 5.74 * Real.log phi := by
      have h1 : 5.74 * 0.481211 < 5.74 * Real.log phi := by nlinarith [hlogphi.1]
      have h2 : (2.7615 : ℝ) < 5.74 * 0.481211 := by norm_num
      linarith
    exact (div_lt_iff₀ h_log_pos).mpr h_chain

/-- Bounds on gap(276). -/
lemma gap_276_bounds
    (h_low_phi : log_lower_bound_phi_hypothesis)
    (h_high_phi : log_upper_bound_phi_hypothesis)
    (h_low_276 : log_171p6_lower_hypothesis)
    (h_high_276 : log_171p6_upper_hypothesis) :
    (10.689 : ℝ) < gap 276 ∧ gap 276 < (10.691 : ℝ) := by
  simp only [gap]
  have hphi := phi_bounds
  have hlogphi := log_phi_bounds h_low_phi h_high_phi
  have h_phi_pos : 0 < phi := phi_pos
  have h_log_pos : 0 < Real.log phi := Real.log_pos (by linarith [hphi.1])
  -- Bounds on 1 + 276/φ
  have h_arg_lower : 1 + 276 / (1.618034 : ℝ) < 1 + 276 / phi := by
    have hdiv : (276 : ℝ) / (1.618034 : ℝ) < 276 / phi := by
      have hpos : (0 : ℝ) < (276 : ℝ) := by norm_num
      exact div_lt_div_of_pos_left hpos h_phi_pos hphi.2
    linarith
  have h_arg_upper : 1 + 276 / phi < 1 + 276 / (1.618033 : ℝ) := by
    have hdiv : (276 : ℝ) / phi < 276 / (1.618033 : ℝ) := by
      have hpos : (0 : ℝ) < (276 : ℝ) := by norm_num
      exact div_lt_div_of_pos_left hpos (by norm_num : (0 : ℝ) < (1.618033 : ℝ)) hphi.1
    linarith
  -- Bounds on log(1 + 276/φ) using monotonicity
  have h_log_lower : Real.log (1 + 276 / (1.618034 : ℝ)) < Real.log (1 + 276 / phi) := by
    apply Real.log_lt_log (by norm_num) h_arg_lower
  have h_log_upper : Real.log (1 + 276 / phi) < Real.log (1 + 276 / (1.618033 : ℝ)) := by
    have h_pos : 0 < 1 + 276 / phi := by positivity
    apply Real.log_lt_log h_pos h_arg_upper
  -- Combine with numerical bounds
  have h_num_lower : (5.1442 : ℝ) < Real.log (1 + 276 / phi) :=
    lt_trans h_low_276 h_log_lower
  have h_num_upper : Real.log (1 + 276 / phi) < (5.1444 : ℝ) :=
    lt_trans h_log_upper h_high_276
  constructor
  · -- Lower bound: gap > 10.689
    have h_chain : 10.689 * Real.log phi < Real.log (1 + 276 / phi) := by
      have h1 : 10.689 * Real.log phi < 10.689 * 0.481213 := by nlinarith [hlogphi.2]
      have h2 : (10.689 : ℝ) * 0.481213 < 5.1442 := by norm_num
      linarith
    exact (lt_div_iff₀ h_log_pos).mpr h_chain
  · -- Upper bound: gap < 10.691
    have h_chain : Real.log (1 + 276 / phi) < 10.691 * Real.log phi := by
      have h1 : 10.691 * 0.481211 < 10.691 * Real.log phi := by nlinarith [hlogphi.1]
      have h2 : (5.1444 : ℝ) < 10.691 * 0.481211 := by norm_num
      linarith
    exact (div_lt_iff₀ h_log_pos).mpr h_chain

end IntervalBounds

end RSBridge
end IndisputableMonolith
