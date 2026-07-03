import IndisputableMonolith.Foundation.DeltaSpine.GoldenInt

/-!
# CostUniqueness: T5 on the φ-ladder, delta-forced (sigma0)

**The choice-free re-derivation of the T5 cost-uniqueness node on its forced
discrete carrier.**

The spine node `Cost.FunctionalEquation.law_of_logic_forces_jcost` proves T5
over `ℝ`: any reciprocal-symmetric, normalized, calibrated, continuous `F`
satisfying the Recognition Composition Law (RCL)

    `F(xy) + F(x/y) = 2·F(x)·F(y) + 2·F(x) + 2·F(y)`

equals `Jcost x = (x + x⁻¹)/2 − 1`. Its axiom closure is
`[propext, Classical.choice, Quot.sound]`: sigma1 (CHOICE).

**The trichotomy read (2026-07-01)** classified that proof's continuum use:
the algebraic skeleton (substitute `x = e^s`, fold the RCL into d'Alembert's
`G(s+t) + G(s−t) = G(s)·G(t)` for `G = 2F + 2`) is pure instance leakage, and
the analytic core (the cosh ODE-uniqueness argument) exists only to exclude
pathological solutions that live on the *uncountable* domain `ℝ`. On the
domain the recognition ledger actually inhabits — the φ-ladder
`{φⁿ : n ∈ ℤ}` forced by T6 self-similarity — no pathology can exist: the
d'Alembert law is a two-step recurrence, and two initial values pin the whole
solution by induction. No continuity axis, no `Classical.choice`.

This module carries that out over `GoldenInt = ℤ[φ]` (see
`DeltaSpine.GoldenInt`, the sigma0 T6 carrier):

1. `phiZpow n = φⁿ` through the unit group `GoldenIntˣ` (negative exponents
   are exact ring elements — `φ⁻¹ = φ − 1` — no division, no field).
2. `traceZ n = φⁿ + φ⁻ⁿ`, the exact ℤ[φ] carrier of `2·cosh(n·log φ)`.
3. `traceZ` satisfies d'Alembert `t(m+n) + t(m−n) = t(m)·t(n)` — a purely
   algebraic identity (existence).
4. Any `h : ℤ → GoldenInt` satisfying d'Alembert with `h 0 = 2`,
   `h 1 = √5 = 2φ − 1` equals `traceZ` (uniqueness, by two-step strong
   induction; symmetry `h(−n) = h(n)` is *derived* from the law, not assumed).
5. `Jdouble n = traceZ n − 2 = 2·J(φⁿ)` satisfies the exact discrete RCL
   `G(m+n) + G(m−n) = G(m)·G(n) + 2·G(m) + 2·G(n)` (the
   `SatisfiesCompositionLaw` shape with `x = φᵐ`, `y = φⁿ`), and is the
   unique such sequence with `G 0 = 0` (normalization) and
   `G 1 = √5 − 2 = 2φ − 3 = 2·J(φ)` (calibration). This is
   `t5_delta_forced`.

**The doubled normalization.** `2` is not invertible in ℤ[φ], so the module
works with `2·J` throughout; the classical `J` is recovered at the display
boundary. With `G = 2F` the classical RCL
`F(xy) + F(x/y) = 2FxFy + 2Fx + 2Fy` becomes exactly
`G(xy) + G(x/y) = GxGy + 2Gx + 2Gy`, which is the `SatisfiesDiscreteRCL`
shape below — no content changes, only the scale.

**Stronger hypotheses ledger than the classical node.** Classically T5 assumes
reciprocal symmetry (`IsReciprocalCost`), normalization, calibration, the RCL,
*and* continuity. Here the inputs are only normalization, calibration, and the
RCL: symmetry is a theorem (`dAlembert_symm`) and the continuity axis does not
exist on ℤ. The continuum tax — interpolating between the ladder rungs and
excluding discontinuous solutions of the real d'Alembert equation — is exactly
what remains sigma1, and it stays quarantined in `Cost.FunctionalEquation`
(and the display bridge `DeltaSpine.GoldenIntReal`:
`toReal (traceZ n) = 2·cosh (n·log φ)`).

**Tactic hygiene** (same measured discipline as `DeltaSpine.GoldenInt`): no
full `simp`, no `omega` on goals with logical structure, case splits by
`rcases`, kernel `decide` on integer literals, `ring` over ℤ[φ] (probed
choice-free), and Mathlib's `Units`/`zpow` machinery (probed:
`[propext, Quot.sound]`).

**Verdict target: sigma0 DELTA_FORCED** — every theorem here must close within
`{propext, Quot.sound}`. Audit with `scripts/sigma_audit.py` or
`#print axioms t5_delta_forced`.

Delta Forcing Spectrum program: `Delta_Forcing_Spectrum_20260626.tex`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace DeltaSpine
namespace GoldenInt

/-! ## Integer powers of φ through the unit group -/

/-- The inverse of φ in ℤ[φ]: `φ⁻¹ = φ − 1 = ⟨−1, 1⟩`. Exact — no division. -/
def phiInv : GoldenInt := ⟨-1, 1⟩

/-- `φ · φ⁻¹ = 1` — kernel computation. -/
theorem phi_mul_phiInv : phi * phiInv = 1 := by decide

/-- `φ⁻¹ · φ = 1` — kernel computation. -/
theorem phiInv_mul_phi : phiInv * phi = 1 := by decide

/-- The golden reciprocal identity `φ⁻¹ = φ − 1`, exact in ℤ[φ]. This is the
    self-similarity `φ² = φ + 1` read multiplicatively. -/
theorem phiInv_eq_phi_sub_one : phiInv = phi - 1 := by decide

/-- φ as a unit of ℤ[φ]. -/
def phiUnit : GoldenIntˣ := ⟨phi, phiInv, phi_mul_phiInv, phiInv_mul_phi⟩

/-- `φⁿ` for `n : ℤ`, through the unit group, so negative exponents are exact
    ring elements. -/
def phiZpow (n : ℤ) : GoldenInt := ((phiUnit ^ n : GoldenIntˣ) : GoldenInt)

/-- The exponential law `φ^(m+n) = φ^m · φ^n`. -/
theorem phiZpow_add (m n : ℤ) : phiZpow (m + n) = phiZpow m * phiZpow n := by
  unfold phiZpow
  rw [zpow_add]
  rfl

theorem phiZpow_zero : phiZpow 0 = 1 := by
  unfold phiZpow
  rw [zpow_zero]
  rfl

theorem phiZpow_one : phiZpow 1 = phi := by
  unfold phiZpow
  rw [zpow_one]
  rfl

theorem phiZpow_neg_one : phiZpow (-1) = phiInv := by
  unfold phiZpow
  rw [zpow_neg_one]
  rfl

/-- `φ⁻ⁿ · φⁿ = 1`: every ladder rung is invertible. -/
theorem phiZpow_neg_mul (n : ℤ) : phiZpow (-n) * phiZpow n = 1 := by
  unfold phiZpow
  rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

/-! ## √5 and the trace sequence -/

/-- `√5` as an exact element of ℤ[φ]: `√5 = 2φ − 1 = ⟨−1, 2⟩`. -/
def sqrtFive : GoldenInt := ⟨-1, 2⟩

theorem sqrtFive_eq : sqrtFive = 2 * phi - 1 := by decide

/-- `(√5)² = 5` — kernel computation, no `Real.sqrt`. -/
theorem sqrtFive_sq : sqrtFive * sqrtFive = 5 := by decide

/-- The trace sequence `t(n) = φⁿ + φ⁻ⁿ`: the exact ℤ[φ] carrier of
    `2·cosh(n·log φ)`. -/
def traceZ (n : ℤ) : GoldenInt := phiZpow n + phiZpow (-n)

theorem traceZ_zero : traceZ 0 = 2 := by
  unfold traceZ
  rw [neg_zero, phiZpow_zero]
  decide

theorem traceZ_one : traceZ 1 = sqrtFive := by
  unfold traceZ
  rw [phiZpow_one, phiZpow_neg_one]
  decide

/-- Reciprocal symmetry of the trace, by construction. -/
theorem traceZ_neg (n : ℤ) : traceZ (-n) = traceZ n := by
  unfold traceZ
  -- generic `neg_neg` on ℤ routes through a choice-tainted instance path;
  -- derive the identity by omega (atomic Int equality, choice-free)
  have e : -(-n) = n := by omega
  rw [e, add_comm]

/-! ## The d'Alembert law: existence and uniqueness -/

/-- The d'Alembert composition law on ℤ-indexed sequences:
    `h(m+n) + h(m−n) = h(m)·h(n)`. This is the `G`-side shape of
    `Cost.FunctionalEquation.composition_law_equiv_coshAdd`, discretized to
    the φ-ladder. -/
def SatisfiesDAlembert (h : ℤ → GoldenInt) : Prop :=
  ∀ m n : ℤ, h (m + n) + h (m - n) = h m * h n

/-- **Existence**: the trace satisfies d'Alembert. A purely algebraic identity
    — expand both sides through the exponential law and `ring`. -/
theorem traceZ_dAlembert : SatisfiesDAlembert traceZ := by
  intro m n
  unfold traceZ
  have h1 : phiZpow (m + n) = phiZpow m * phiZpow n := phiZpow_add m n
  have h2 : phiZpow (-(m + n)) = phiZpow (-m) * phiZpow (-n) := by
    have e : -(m + n) = -m + -n := by ring
    rw [e, phiZpow_add]
  have h3 : phiZpow (m - n) = phiZpow m * phiZpow (-n) := by
    have e : m - n = m + -n := by ring
    rw [e, phiZpow_add]
  have h4 : phiZpow (-(m - n)) = phiZpow (-m) * phiZpow n := by
    have e : -(m - n) = -m + n := by ring
    rw [e, phiZpow_add]
  rw [h1, h2, h3, h4]
  ring

/-- Reciprocal symmetry is **derived** from the law and normalization (the
    classical node has to assume it as `IsReciprocalCost`): put `m = 0` in
    d'Alembert and cancel. -/
theorem dAlembert_symm (h : ℤ → GoldenInt) (h0 : h 0 = 2)
    (hd : SatisfiesDAlembert h) : ∀ n : ℤ, h (-n) = h n := by
  intro n
  have hh := hd 0 n
  rw [zero_add, zero_sub, h0] at hh
  -- hh : h n + h (-n) = 2 * h n
  have h2 : h n + h (-n) = h n + h n := by rw [hh]; ring
  exact add_left_cancel h2

/-- The two-step recurrence hiding in d'Alembert: put `n = 1`, so
    `h(k+2) = √5·h(k+1) − h(k)`. This is what replaces the cosh ODE on ℤ:
    a second-order recurrence needs exactly two initial values. -/
theorem dAlembert_step (h : ℤ → GoldenInt) (h1 : h 1 = sqrtFive)
    (hd : SatisfiesDAlembert h) (n : ℤ) :
    h (n + 2) = sqrtFive * h (n + 1) - h n := by
  have hh := hd (n + 1) 1
  have e1 : n + 1 + 1 = n + 2 := by ring
  have e2 : n + 1 - 1 = n := by ring
  rw [e1, e2, h1] at hh
  -- hh : h (n + 2) + h n = h (n + 1) * sqrtFive
  have h3 : h (n + 2) = h (n + 1) * sqrtFive - h n := eq_sub_of_add_eq hh
  rw [h3]; ring

/-- The trace satisfies the recurrence (existence instantiated). -/
theorem traceZ_step (n : ℤ) :
    traceZ (n + 2) = sqrtFive * traceZ (n + 1) - traceZ n :=
  dAlembert_step traceZ traceZ_one traceZ_dAlembert n

/-- **Uniqueness**: any sequence satisfying d'Alembert with the trace's two
    initial values *is* the trace. Two-step strong induction on ℕ, then the
    derived symmetry extends to all of ℤ. This is the sigma0 replacement for
    `ode_cosh_uniqueness_contdiff`: on the discrete carrier the recurrence
    leaves no room for pathological solutions, so no continuity hypothesis
    and no choice-dependent analysis are needed. -/
theorem dAlembert_unique (h : ℤ → GoldenInt)
    (h0 : h 0 = 2) (h1 : h 1 = sqrtFive)
    (hd : SatisfiesDAlembert h) :
    ∀ n : ℤ, h n = traceZ n := by
  have key : ∀ k : ℕ, h (k : ℤ) = traceZ (k : ℤ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases k with _ | _ | k
      · show h 0 = traceZ 0
        rw [h0, traceZ_zero]
      · show h 1 = traceZ 1
        rw [h1, traceZ_one]
      · show h ((k + 2 : ℕ) : ℤ) = traceZ ((k + 2 : ℕ) : ℤ)
        have e2 : ((k + 2 : ℕ) : ℤ) = (k : ℤ) + 2 := by omega
        have e1 : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
        have ihk : h (k : ℤ) = traceZ (k : ℤ) := ih k (by omega)
        have ihk1 : h ((k : ℤ) + 1) = traceZ ((k : ℤ) + 1) := by
          rw [← e1]
          exact ih (k + 1) (by omega)
        rw [e2, dAlembert_step h h1 hd, traceZ_step, ihk, ihk1]
  intro n
  rcases n with k | k
  · exact key k
  · have e : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := rfl
    rw [e, dAlembert_symm h h0 hd, traceZ_neg]
    exact key (k + 1)

/-! ## The J-cost form: the discrete Recognition Composition Law -/

/-- The discrete RCL over ℤ[φ]: the exact shape of
    `Cost.FunctionalEquation.SatisfiesCompositionLaw` with `x = φᵐ`, `y = φⁿ`
    (so `x·y = φ^(m+n)`, `x/y = φ^(m−n)`), in the doubled normalization
    `G = 2F` that keeps everything inside the ring. -/
def SatisfiesDiscreteRCL (G : ℤ → GoldenInt) : Prop :=
  ∀ m n : ℤ, G (m + n) + G (m - n) = G m * G n + 2 * G m + 2 * G n

/-- The doubled J-cost on the φ-ladder:
    `Jdouble n = φⁿ + φ⁻ⁿ − 2 = 2·J(φⁿ)` where `J(x) = (x + x⁻¹)/2 − 1`. -/
def Jdouble (n : ℤ) : GoldenInt := traceZ n - 2

/-- Normalization: `2·J(φ⁰) = 2·J(1) = 0`. -/
theorem Jdouble_zero : Jdouble 0 = 0 := by
  unfold Jdouble
  rw [traceZ_zero]
  ring

/-- Calibration: `2·J(φ) = φ + φ⁻¹ − 2 = √5 − 2 = 2φ − 3`. -/
theorem Jdouble_one : Jdouble 1 = sqrtFive - 2 := by
  unfold Jdouble
  rw [traceZ_one]

/-- Reciprocal symmetry `2·J(φ⁻ⁿ) = 2·J(φⁿ)`, inherited from the trace. -/
theorem Jdouble_symm (n : ℤ) : Jdouble (-n) = Jdouble n := by
  unfold Jdouble
  rw [traceZ_neg]

/-- **Existence**: the doubled J-cost satisfies the discrete RCL. Linear
    rearrangement of the d'Alembert identity. -/
theorem Jdouble_rcl : SatisfiesDiscreteRCL Jdouble := by
  intro m n
  unfold Jdouble
  have hd := traceZ_dAlembert m n
  have expand : (traceZ m - 2) * (traceZ n - 2) + 2 * (traceZ m - 2)
      + 2 * (traceZ n - 2) = traceZ m * traceZ n - 4 := by ring
  rw [expand, ← hd]
  ring

/-- **Uniqueness**: any sequence satisfying the discrete RCL with the J-cost's
    normalization and calibration *is* the doubled J-cost. Shift by 2 into the
    d'Alembert frame and apply trace uniqueness. -/
theorem discreteRCL_unique (G : ℤ → GoldenInt)
    (hnorm : G 0 = 0)
    (hcalib : G 1 = sqrtFive - 2)
    (hcomp : SatisfiesDiscreteRCL G) :
    ∀ n : ℤ, G n = Jdouble n := by
  have h0 : (fun k : ℤ => G k + 2) 0 = 2 := by
    show G 0 + 2 = 2
    rw [hnorm]; ring
  have h1 : (fun k : ℤ => G k + 2) 1 = sqrtFive := by
    show G 1 + 2 = sqrtFive
    rw [hcalib]; ring
  have hd : SatisfiesDAlembert (fun k : ℤ => G k + 2) := by
    intro m n
    show G (m + n) + 2 + (G (m - n) + 2) = (G m + 2) * (G n + 2)
    have hc := hcomp m n
    have expand : (G m + 2) * (G n + 2)
        = G m * G n + 2 * G m + 2 * G n + 4 := by ring
    rw [expand, ← hc]
    ring
  have key := dAlembert_unique (fun k : ℤ => G k + 2) h0 h1 hd
  intro n
  have hk : G n + 2 = traceZ n := key n
  unfold Jdouble
  rw [← hk]
  ring

/-! ## The T5 forcing theorem, delta-forced -/

/-- **T5, DELTA-FORCED (sigma0)**: on the φ-ladder forced by T6, the doubled
    J-cost `Jdouble n = φⁿ + φ⁻ⁿ − 2 = 2·J(φⁿ)`

    1. is normalized (`Jdouble 0 = 0`),
    2. is calibrated (`Jdouble 1 = √5 − 2 = 2·J(φ)`),
    3. is reciprocal-symmetric (**derived**, not assumed),
    4. satisfies the discrete Recognition Composition Law, and
    5. is the **unique** sequence doing so given only normalization,
       calibration, and the law.

    This is the content of `law_of_logic_forces_jcost` restricted to the
    domain the ledger actually inhabits, with the continuum stripped away:
    no continuity hypothesis (the axis does not exist on ℤ), no reciprocity
    hypothesis (it is a theorem), no `Classical.choice` (audit:
    `{propext, Quot.sound}`). The remaining classical content — that among
    *continuous* interpolants of the ladder the cosh family is unique — is
    exactly the sigma1 residue quarantined in `Cost.FunctionalEquation`. -/
theorem t5_delta_forced :
    (Jdouble 0 = 0 ∧
     Jdouble 1 = sqrtFive - 2 ∧
     (∀ n : ℤ, Jdouble (-n) = Jdouble n) ∧
     SatisfiesDiscreteRCL Jdouble) ∧
    (∀ G : ℤ → GoldenInt,
      G 0 = 0 →
      G 1 = sqrtFive - 2 →
      SatisfiesDiscreteRCL G →
      ∀ n : ℤ, G n = Jdouble n) :=
  ⟨⟨Jdouble_zero, Jdouble_one, Jdouble_symm, Jdouble_rcl⟩, discreteRCL_unique⟩

end GoldenInt
end DeltaSpine
end Foundation
end IndisputableMonolith
