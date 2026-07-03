import Mathlib

/-!
# Fourier-Space Subsequential Extraction (Proved)

Cantor diagonal extraction for bounded sequences in proper metric spaces.
All results proved — no sorry, no axiom.

## Main result

`nat_diagonal_extraction`: Given `f : ℕ → ℕ → X` bounded in a proper space,
∃ φ (strictly increasing) and g such that f(φ(n), m) → g(m) for every m.
-/

namespace IndisputableMonolith.NavierStokes.FourierExtraction

open Filter Topology

theorem tendsto_comp_strictMono {X : Type*} [TopologicalSpace X]
    {f : ℕ → X} {x : X} (hf : Tendsto f atTop (𝓝 x))
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    Tendsto (f ∘ ψ) atTop (𝓝 x) :=
  hf.comp hψ.tendsto_atTop

theorem strictMono_id_le {φ : ℕ → ℕ} (hφ : StrictMono φ) : ∀ n, n ≤ φ n := by
  intro n; induction n with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_of_le le_rfl)))

theorem bounded_subseq_tendsto {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : ℕ → X) (c : X) (R : ℝ) (hf : ∀ n, dist (f n) c ≤ R) :
    ∃ (φ : ℕ → ℕ) (x : X), StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 x) := by
  by_cases hR : 0 ≤ R
  · obtain ⟨x, _, φ, hφ, htend⟩ := (isCompact_closedBall c R).tendsto_subseq
      (fun n => Metric.mem_closedBall.mpr (hf n))
    exact ⟨φ, x, hφ, htend⟩
  · exact absurd (le_trans dist_nonneg (hf 0)) (not_le.mpr (lt_of_not_le hR))

section Diagonal

variable {X : Type*} [MetricSpace X] [ProperSpace X]
variable (f : ℕ → ℕ → X) (c : X) (R : ℝ) (hf : ∀ n m, dist (f n m) c ≤ R)

/-- Composed extraction at step m: makes columns 0..m converge. -/
private noncomputable def CE : ℕ → (ℕ → ℕ)
  | 0 => (bounded_subseq_tendsto (fun n => f n 0) c R (fun n => hf n 0)).choose
  | m + 1 =>
    let φ := CE m
    let ψ := (bounded_subseq_tendsto (fun n => f (φ n) (m + 1)) c R
                (fun n => hf (φ n) (m + 1))).choose
    φ ∘ ψ

/-- Limit at column m. -/
private noncomputable def CL : ℕ → X
  | 0 => (bounded_subseq_tendsto (fun n => f n 0) c R (fun n => hf n 0)).choose_spec.choose
  | m + 1 =>
    (bounded_subseq_tendsto (fun n => f (CE f c R hf m n) (m + 1)) c R
      (fun n => hf (CE f c R hf m n) (m + 1))).choose_spec.choose

/-- The "local" extraction at step m+1. -/
private noncomputable def LE (m : ℕ) : ℕ → ℕ :=
  (bounded_subseq_tendsto (fun n => f (CE f c R hf m n) (m + 1)) c R
    (fun n => hf (CE f c R hf m n) (m + 1))).choose

private theorem CE_zero : CE f c R hf 0 =
    (bounded_subseq_tendsto (fun n => f n 0) c R (fun n => hf n 0)).choose := rfl

private theorem CE_succ (m : ℕ) : CE f c R hf (m + 1) = CE f c R hf m ∘ LE f c R hf m := rfl

private theorem LE_strictMono (m : ℕ) : StrictMono (LE f c R hf m) :=
  (bounded_subseq_tendsto (fun n => f (CE f c R hf m n) (m + 1)) c R
    (fun n => hf (CE f c R hf m n) (m + 1))).choose_spec.choose_spec.1

private theorem CE_strictMono : ∀ m, StrictMono (CE f c R hf m) := by
  intro m; induction m with
  | zero =>
    exact (bounded_subseq_tendsto (fun n => f n 0) c R (fun n => hf n 0)).choose_spec.choose_spec.1
  | succ k ih =>
    rw [CE_succ]; exact ih.comp (LE_strictMono f c R hf k)

private theorem LE_conv (m : ℕ) :
    Tendsto (fun n => f (CE f c R hf m (LE f c R hf m n)) (m + 1)) atTop
      (𝓝 (CL f c R hf (m + 1))) :=
  (bounded_subseq_tendsto (fun n => f (CE f c R hf m n) (m + 1)) c R
    (fun n => hf (CE f c R hf m n) (m + 1))).choose_spec.choose_spec.2

private theorem CE_conv_at : ∀ m, Tendsto (fun n => f (CE f c R hf m n) m)
    atTop (𝓝 (CL f c R hf m)) := by
  intro m; cases m with
  | zero =>
    exact (bounded_subseq_tendsto (fun n => f n 0) c R (fun n => hf n 0)).choose_spec.choose_spec.2
  | succ k => exact LE_conv f c R hf k

private theorem CE_conv_le : ∀ m j, j ≤ m →
    Tendsto (fun n => f (CE f c R hf m n) j) atTop (𝓝 (CL f c R hf j)) := by
  intro m j hj
  induction m with
  | zero =>
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0; exact CE_conv_at f c R hf 0
  | succ k ih =>
    rcases eq_or_lt_of_le hj with hjk | hjk
    · subst hjk; exact CE_conv_at f c R hf (k + 1)
    · rw [CE_succ]
      exact tendsto_comp_strictMono (ih (Nat.lt_succ_iff.mp hjk)) (LE_strictMono f c R hf k)

/-- Factoring: CE(m+p) = CE(m) ∘ ρ with ρ strictly increasing and ρ(k) ≥ k. -/
private theorem CE_factor (m p : ℕ) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ (∀ k, k ≤ ρ k) ∧
      ∀ k, CE f c R hf (m + p) k = CE f c R hf m (ρ k) := by
  induction p with
  | zero => exact ⟨id, strictMono_id, fun k => le_refl k, fun _ => rfl⟩
  | succ q ih =>
    obtain ⟨ρ, hρ_mono, hρ_ge, hρ_eq⟩ := ih
    refine ⟨ρ ∘ LE f c R hf (m + q),
      hρ_mono.comp (LE_strictMono f c R hf (m + q)),
      fun k => le_trans (strictMono_id_le (LE_strictMono f c R hf (m + q)) k)
        (hρ_ge (LE f c R hf (m + q) k)),
      fun k => ?_⟩
    show CE f c R hf (m + (q + 1)) k = CE f c R hf m ((ρ ∘ LE f c R hf (m + q)) k)
    have h1 : m + (q + 1) = (m + q) + 1 := by omega
    rw [h1, CE_succ]
    simp only [Function.comp_apply]
    exact hρ_eq _

private noncomputable def D : ℕ → ℕ := fun n => CE f c R hf n n

private theorem D_succ_gt (n : ℕ) : D f c R hf n < D f c R hf (n + 1) := by
  show CE f c R hf n n < CE f c R hf (n + 1) (n + 1)
  rw [CE_succ]
  show CE f c R hf n n < CE f c R hf n (LE f c R hf n (n + 1))
  exact CE_strictMono f c R hf n
    (lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl)
      (strictMono_id_le (LE_strictMono f c R hf n) (n + 1)))

private theorem D_strictMono : StrictMono (D f c R hf) :=
  strictMono_nat_of_lt_succ (fun n => D_succ_gt f c R hf n)

private theorem D_converges (m : ℕ) :
    Tendsto (fun n => f (D f c R hf n) m) atTop (𝓝 (CL f c R hf m)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h_base := CE_conv_at f c R hf m
  rw [Metric.tendsto_atTop] at h_base
  obtain ⟨K, hK⟩ := h_base ε hε
  refine ⟨max m K, fun n hn => ?_⟩
  have hm : m ≤ n := le_of_max_le_left hn
  have hK_le : K ≤ n := le_of_max_le_right hn
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨ρ, _hρ_mono, hρ_ge, hρ_eq⟩ := CE_factor f c R hf m p
  show dist (f (CE f c R hf (m + p) (m + p)) m) (CL f c R hf m) < ε
  rw [hρ_eq (m + p)]
  exact hK (ρ (m + p)) (le_trans hK_le (hρ_ge (m + p)))

end Diagonal

/-- **Cantor diagonal extraction** for ℕ-indexed bounded sequences
in a proper metric space. Fully proved. -/
theorem nat_diagonal_extraction {X : Type*} [MetricSpace X] [ProperSpace X]
    (f : ℕ → ℕ → X) (c : X) (R : ℝ)
    (hf : ∀ n m, dist (f n m) c ≤ R) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → X), StrictMono φ ∧
      ∀ m, Tendsto (fun n => f (φ n) m) atTop (𝓝 (g m)) :=
  ⟨D f c R hf, CL f c R hf, D_strictMono f c R hf, D_converges f c R hf⟩

end IndisputableMonolith.NavierStokes.FourierExtraction
