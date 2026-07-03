import Mathlib

namespace IndisputableMonolith
namespace MaxwellDEC

/-- Oriented k-simplex (abstract id). -/
structure Simplex (α : Type) (k : Nat) where
  id     : α
  orient : Bool

/-- Discrete k-form: value per oriented k-simplex. -/
@[simp] def DForm (α : Type) (k : Nat) := Simplex α k → ℝ

/-- Coboundary operator interface on the mesh. -/
class HasCoboundary (α : Type) where
  d : ∀ {k : Nat}, DForm α k → DForm α (k+1)
  d_zero : ∀ {k}, d (fun (_ : Simplex α k) => 0) = (fun _ => 0)

/-- Hodge star interface (metric/constitutive).
    We expose linearity and a signature-correct involution law `⋆⋆ = σ(k) · id`.
    The `σ` function captures the metric signature effect; for example in 4D
    Riemannian one may take `σ k = (-1)^(k*(4-k))`, while in Lorentzian (−,+,+,+)
    one would use `σ k = (-1)^(k*(4-k)+1)`. We keep this abstract so concrete
    meshes can choose either. -/
class HasHodge (α : Type) where
  n : Nat
  star : ∀ {k : Nat}, DForm α k → DForm α (n - k)
  star_add : ∀ {k} (x y : DForm α k), star (fun s => x s + y s) = (fun s => star x s + star y s)
  star_zero : ∀ {k}, star (fun (_ : Simplex α k) => 0) = (fun _ => 0)
  star_smul : ∀ {k} (c : ℝ) (x : DForm α k), star (fun s => c * x s) = (fun s => c * (star x s))
  signature : Nat → ℝ
  star_star : ∀ {k} (h : n - (n - k) = k) (x : DForm α k),
    h ▸ (star (star x)) = (fun s => signature k * x s)
  /-- Optional positivity control on 2-forms (useful in 4D Riemannian media).
      Requires n = 4 so that star maps 2-forms to 2-forms.
      Instances targeting Lorentzian signatures can simply provide a trivial
      proof such as `by intro; intro; exact le_of_eq (by ring)` if not used. -/
  star2_psd : ∀ (h : n - 2 = 2) (x : DForm α 2) (s : Simplex α 2),
    0 ≤ x s * (h ▸ (star x)) s

/-- Linear medium parameters. -/
structure Medium (α : Type) [HasHodge α] where
  eps : ℝ
  mu  : ℝ

/-- Sources (charge and current). -/
structure Sources (α : Type) where
  ρ : DForm α 0
  J : DForm α 1

variable {α : Type}

/-- Quasi-static Maxwell equations on the mesh (no time derivative terms).
    Faraday and Gauss-M are stated cleanly. Constitutive relations (const_D, const_B)
    and source equations (ampere_qs, gauss_e) require dimension n=3 for form-degree
    alignment, so they are parameterized by the dimension hypothesis `hn`. -/
structure Equations (α : Type) [HasCoboundary α] [inst : HasHodge α] (M : Medium α) where
  E : DForm α 1
  H : DForm α 1
  B : DForm α 2
  D : DForm α 2
  src : Sources α
  /-- Faraday QS: curl E = 0 (no time-varying B in quasistatic limit) -/
  faraday_qs : HasCoboundary.d E = fun _ => 0
  /-- Ampere QS: d H = star J (requires n-1=2 for form-degree alignment) -/
  ampere_qs  : ∀ (hn : inst.n - 1 = 2),
    HasCoboundary.d H = cast (congrArg (DForm α) hn) (HasHodge.star src.J)
  /-- Gauss E: d D = star rho (requires n-0=3 for form-degree alignment) -/
  gauss_e    : ∀ (hn : inst.n - 0 = 3),
    HasCoboundary.d D = cast (congrArg (DForm α) hn) (HasHodge.star src.ρ)
  /-- Gauss M: div B = 0 (no magnetic monopoles) -/
  gauss_m    : HasCoboundary.d B = fun _ => 0
  /-- Constitutive: D = ε⋆E (requires n-1=2 for form-degree alignment) -/
  const_D    : ∀ (hn : inst.n - 1 = 2), D = hn ▸ (fun s => M.eps * HasHodge.star E s)
  /-- Constitutive: B = μ⋆H (requires n-1=2 for form-degree alignment) -/
  const_B    : ∀ (hn : inst.n - 1 = 2), B = hn ▸ (fun s => M.mu * HasHodge.star H s)

/-- Pointwise Hodge energy density for 2-forms: ω · (⋆ω) on each 2-simplex.
    Requires n = 4 (spacetime dimension). -/
def energy2 (ω : DForm α 2) [inst : HasHodge α] (h : inst.n - 2 = 2) : DForm α 2 :=
  fun s => ω s * (h ▸ (HasHodge.star (k:=2) ω)) s

/-- Admissibility: strictly positive material parameters. -/
def Admissible [HasHodge α] (M : Medium α) : Prop := 0 < M.eps ∧ 0 < M.mu

/-- Positivity of the Hodge energy density for admissible media, provided the
    instance supplies `star2_psd`. This is signature-agnostic and delegates the
    sign choice to the instance via `star2_psd`. -/
theorem energy2_nonneg_pointwise
  [inst : HasHodge α] (h : inst.n - 2 = 2) (M : Medium α) (hadm : Admissible (α:=α) M) (ω : DForm α 2)
  : ∀ s, 0 ≤ energy2 (α:=α) ω h s := by
  intro s
  have hpsd := HasHodge.star2_psd (α:=α) h ω s
  simp [energy2]
  exact hpsd

/-- PEC boundary descriptor (edges where tangential E vanishes). -/
structure PEC (β : Type) where
  boundary1 : Set (Simplex β 1)

end MaxwellDEC
end IndisputableMonolith
