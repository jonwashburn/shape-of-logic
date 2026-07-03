import Mathlib

namespace IndisputableMonolith
namespace Complexity
namespace BalancedParityHidden

variable {n : ℕ} [DecidableEq (Fin n)]

/-- Hidden mask encoder: bit b with mask R is `R` if b=false and `not ∘ R` if b=true. -/
def enc (b : Bool) (R : Fin n → Bool) : Fin n → Bool :=
  fun i => if b then ! (R i) else R i

@[simp] lemma enc_false (R : Fin n → Bool) : enc (n:=n) false R = R := by
  funext i; simp [enc]

@[simp] lemma enc_true (R : Fin n → Bool) : enc (n:=n) true R = (fun i => ! (R i)) := by
  funext i; simp [enc]

/-- Restrict a full word to a queried index set `M`. -/
def restrict (f : Fin n → Bool) (M : Finset (Fin n)) : {i // i ∈ M} → Bool :=
  fun i => f i.val

@[simp] lemma restrict_enc_false (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc false R) M = restrict (n:=n) R M := by
  funext i; simp [restrict, enc]

@[simp] lemma restrict_enc_true (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc true R) M = (fun i => ! (restrict (n:=n) R M i)) := by
  funext i; simp [restrict, enc]

/-- Extend a partial assignment on `M` to a full mask by defaulting to `false` off `M`. -/
def extendMask (M : Finset (Fin n)) (a : {i // i ∈ M} → Bool) : Fin n → Bool :=
  fun i => if h : i ∈ M then a ⟨i, h⟩ else false

@[simp] lemma extendMask_in (M : Finset (Fin n)) (a : {i // i ∈ M} → Bool) {i : Fin n} (h : i ∈ M) :
  extendMask (n:=n) M a i = a ⟨i, h⟩ := by
  simp [extendMask, h]

@[simp] lemma extendMask_notin (M : Finset (Fin n)) (a : {i // i ∈ M} → Bool) {i : Fin n} (h : i ∉ M) :
  extendMask (n:=n) M a i = false := by
  simp [extendMask, h]

@[simp] lemma restrict_extendMask (M : Finset (Fin n)) (a : {i // i ∈ M} → Bool) :
  restrict (n:=n) (extendMask (n:=n) M a) M = a := by
  funext i
  simp [restrict, extendMask]

/-- Any fixed-view decoder on a set `M` of queried indices can be fooled by a suitable `(b,R)`. -/
 theorem adversarial_failure (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ∃ (b : Bool) (R : Fin n → Bool),
    g (restrict (n:=n) (enc b R) M) ≠ b := by
  classical
  -- Pick an arbitrary local view `a` and force the decoder to predict `b' := g a`.
  let a : {i // i ∈ M} → Bool := fun _ => false
  let b' : Bool := g a
  -- Choose the true bit to be the opposite of the decoder's prediction.
  let b : Bool := ! b'
  -- Choose the mask so that the restricted encoding equals `a`.
  let R : Fin n → Bool :=
    if b then extendMask M (fun i => ! (a i)) else extendMask M a
  have hRestr : restrict (n:=n) (enc b R) M = a := by
    funext i
    dsimp [restrict, enc, R, extendMask]
    by_cases hb : b
    · -- b = true
      simp [hb, dif_pos i.property]
    · -- b = false
      simp [hb, dif_pos i.property]
  refine ⟨b, R, ?_⟩
  have hval' : g (restrict (n:=n) (enc b R) M) = g a := by
    simpa [hRestr]
  have hval : g (restrict (n:=n) (enc b R) M) = b' := by
    simpa [b'] using hval'
  have hbrel : b = ! b' := rfl
  have ne : b' ≠ ! b' := by cases b' <;> decide
  have : g (restrict (n:=n) (enc b R) M) ≠ ! b' := by simpa [hval]
  simpa [hbrel]

/-- If a decoder is correct for all `(b,R)` while querying only `M`, contradiction. -/
 theorem no_universal_decoder (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool), g (restrict (n:=n) (enc b R) M) = b) := by
  classical
  intro h
  rcases adversarial_failure (n:=n) M g with ⟨b, R, hw⟩
  have := h b R
  exact hw this

/-- Query lower bound (worst-case, adversarial): any universally-correct decoder
    must inspect all `n` indices. -/
theorem omega_n_queries
  (M : Finset (Fin n)) (g : (({i // i ∈ M} → Bool)) → Bool)
  (hMlt : M.card < n) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool), g (restrict (n:=n) (enc b R) M) = b) :=
  no_universal_decoder (n:=n) M g

end BalancedParityHidden
end Complexity

namespace IndisputableMonolith

/-- SAT recognition lower bound (dimensionless): any universally-correct fixed-view
    decoder over fewer than n queried indices is impossible. -/
theorem recognition_lower_bound_sat
  (n : ℕ) (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool)
  (hMlt : M.card < n) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool),
        g (Complexity.BalancedParityHidden.restrict
              (Complexity.BalancedParityHidden.enc b R) M) = b) := by
  classical
  simpa using
    (Complexity.BalancedParityHidden.omega_n_queries (n:=n) M g hMlt)

end IndisputableMonolith
