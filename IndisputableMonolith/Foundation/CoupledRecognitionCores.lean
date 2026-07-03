import Mathlib

open scoped BigOperators

namespace IndisputableMonolith
namespace Foundation
namespace CoupledRecognitionCores

noncomputable section

/-- The local quarter-turn core is modeled as a ququart carrier. -/
abbrev QuquartState := Fin 4 → ℂ

/-- The standard basis ket `|m⟩`. -/
def basisKet (m : Fin 4) : QuquartState :=
  fun n => if n = m then 1 else 0

/-- Previous index modulo `4`; this realizes the shift convention
`X|m⟩ = |m+1 mod 4⟩`. -/
def prev4 (m : Fin 4) : Fin 4 :=
  ⟨(m.val + 3) % 4, by omega⟩

/-- Addition modulo `4`. -/
def add4 (a b : Fin 4) : Fin 4 :=
  ⟨(a.val + b.val) % 4, by omega⟩

/-- Subtraction modulo `4`. -/
def sub4 (a b : Fin 4) : Fin 4 :=
  ⟨(a.val + (4 - b.val)) % 4, by omega⟩

/-- Mod-4 subtraction undoes mod-4 addition. -/
theorem sub4_add4_cancel_core (a s : Fin 4) :
    sub4 (add4 a s) a = s := by
  fin_cases a <;> fin_cases s <;> rfl

/-- Mod-4 addition undoes mod-4 subtraction. -/
theorem add4_sub4_cancel_core (m a : Fin 4) :
    add4 a (sub4 m a) = m := by
  fin_cases m <;> fin_cases a <;> rfl

/-- For fixed `s`, the left addend is recoverable from `add4 a s`. -/
theorem add4_eq_add4_iff_left_core (a a' s : Fin 4) :
    add4 a s = add4 a' s ↔ a = a' := by
  fin_cases a <;> fin_cases a' <;> fin_cases s <;> decide

/-- The canonical ququart shift operator `X`. -/
def ququartX : QuquartState →ₗ[ℂ] QuquartState where
  toFun := fun ψ m => ψ (prev4 m)
  map_add' := by
    intro ψ χ
    ext m
    simp [prev4]
  map_smul' := by
    intro a ψ
    ext m
    simp [prev4]

/-- The canonical ququart phase operator `Z`. -/
def ququartZ : QuquartState →ₗ[ℂ] QuquartState where
  toFun := fun ψ m => Complex.I ^ m.val * ψ m
  map_add' := by
    intro ψ χ
    ext m
    simp
    ring
  map_smul' := by
    intro a ψ
    ext m
    simp
    ring

/-- `X|m⟩ = |m+1 mod 4⟩`. -/
theorem ququartX_basisKet (m : Fin 4) :
    ququartX (basisKet m) = basisKet (add4 1 m) := by
  ext n
  fin_cases n <;> fin_cases m <;> simp [ququartX, basisKet, prev4, add4]

/-- `Z|m⟩ = i^m |m⟩`. -/
theorem ququartZ_basisKet (m : Fin 4) :
    ququartZ (basisKet m) = (Complex.I ^ m.val) • basisKet m := by
  ext n
  by_cases h : n = m
  · simp [basisKet, ququartZ, h]
  · simp [basisKet, ququartZ, h]

/-- Pointwise Weyl relation `ZX ψ = i XZ ψ`. -/
lemma ququartWeyl_relation_apply (ψ : QuquartState) :
    ququartZ (ququartX ψ) = (Complex.I : ℂ) • ququartX (ququartZ ψ) := by
  ext m
  fin_cases m
  · simp [ququartZ, ququartX, prev4]
    symm
    have hI : Complex.I * Complex.I = (-1 : ℂ) := by
      have h := Complex.I_sq; rw [sq] at h; exact h
    calc
      -(Complex.I * (Complex.I * ψ 3)) = -((Complex.I * Complex.I) * ψ 3) := by ring
      _ = -((-1) * ψ 3) := by rw [hI]
      _ = ψ 3 := by ring
  · simp [ququartZ, ququartX, prev4]
  · simp [ququartZ, ququartX, prev4]
    have hI : Complex.I * Complex.I = (-1 : ℂ) := by
      have h := Complex.I_sq; rw [sq] at h; exact h
    calc
      -ψ 1 = (-1 : ℂ) * ψ 1 := by ring
      _ = (Complex.I * Complex.I) * ψ 1 := by rw [hI]
      _ = Complex.I * (Complex.I * ψ 1) := by ring
  · simp [ququartZ, ququartX, prev4, Complex.I_sq]

/-- The ququart Weyl relation `ZX = iXZ`. -/
theorem ququartWeyl_relation :
    ququartZ.comp ququartX = (Complex.I : ℂ) • (ququartX.comp ququartZ) := by
  apply LinearMap.ext
  intro ψ
  exact ququartWeyl_relation_apply ψ

/-- The finite-site configuration space of coupled ququart cores. -/
abbrev CoupledCoreIndex (N : ℕ) := Fin N → Fin 4

/-- The concrete Hilbert carrier of `N` coupled recognition cores. -/
abbrev CoupledCoreSpace (N : ℕ) := CoupledCoreIndex N → ℂ

/-- The dimension of the coupled-core index space is exactly `4^N`. -/
theorem coupledCoreIndex_card (N : ℕ) :
    Fintype.card (CoupledCoreIndex N) = 4 ^ N := by
  simp [CoupledCoreIndex]

/-- The phase character appearing in the tensor-Weyl monomial. -/
def phaseCharacter {N : ℕ} (b s : CoupledCoreIndex N) : ℂ :=
  Finset.univ.prod fun x : Fin N => Complex.I ^ ((b x).val * (s x).val)

/-- Shift a coupled-core configuration by a finite ququart displacement. -/
def shiftedConfig {N : ℕ} (a s : CoupledCoreIndex N) : CoupledCoreIndex N :=
  fun x => sub4 (s x) (a x)

/-- Add a coupled-core displacement to a configuration. -/
def addedConfig {N : ℕ} (a s : CoupledCoreIndex N) : CoupledCoreIndex N :=
  fun x => add4 (a x) (s x)

/-- Zero phase character. -/
lemma phaseCharacter_zero {N : ℕ} (s : CoupledCoreIndex N) :
    phaseCharacter 0 s = 1 := by
  simp [phaseCharacter]

/-- Zero displacement leaves a coupled-core configuration unchanged. -/
lemma shiftedConfig_zero {N : ℕ} (s : CoupledCoreIndex N) :
    shiftedConfig 0 s = s := by
  funext x
  apply Fin.ext
  simp [shiftedConfig, sub4]

/-- Shifting after adding the same displacement returns the original configuration. -/
theorem shiftedConfig_addedConfig {N : ℕ} (a s : CoupledCoreIndex N) :
    shiftedConfig a (addedConfig a s) = s := by
  funext x
  exact sub4_add4_cancel_core (a x) (s x)

/-- Adding after shifting the same displacement returns the original configuration. -/
theorem addedConfig_shiftedConfig {N : ℕ} (a s : CoupledCoreIndex N) :
    addedConfig a (shiftedConfig a s) = s := by
  funext x
  exact add4_sub4_cancel_core (s x) (a x)

/-- For fixed `s`, the displacement label is recoverable from `addedConfig a s`. -/
theorem addedConfig_eq_addedConfig_iff_left {N : ℕ}
    (a a' s : CoupledCoreIndex N) :
    addedConfig a s = addedConfig a' s ↔ a = a' := by
  constructor
  · intro h
    funext x
    exact (add4_eq_add4_iff_left_core (a x) (a' x) (s x)).mp (congrArg (fun f => f x) h)
  · intro h
    subst h
    rfl

/-- The tensor-Weyl monomial on the concrete coupled-core carrier. -/
def tensorWeylMonomial {N : ℕ} (a b : CoupledCoreIndex N) :
    CoupledCoreSpace N →ₗ[ℂ] CoupledCoreSpace N where
  toFun := fun ψ s => phaseCharacter b s * ψ (shiftedConfig a s)
  map_add' := by
    intro ψ χ
    ext s
    simp [phaseCharacter]
    ring
  map_smul' := by
    intro z ψ
    ext s
    simp [phaseCharacter]
    ring

/-- The trivial Weyl monomial is the identity. -/
theorem tensorWeylMonomial_zero_zero {N : ℕ} :
    tensorWeylMonomial (N := N) 0 0 = LinearMap.id := by
  ext ψ s
  simp [tensorWeylMonomial, phaseCharacter_zero, shiftedConfig_zero]

/-- Standard basis ket for the coupled-core carrier. -/
def coupledBasisKet {N : ℕ} (s : CoupledCoreIndex N) : CoupledCoreSpace N :=
  fun t => if t = s then 1 else 0

/-- The coupled standard basis is orthonormal for the explicit finite sum. -/
theorem coupledBasisKet_orthonormal {N : ℕ} (s t : CoupledCoreIndex N) :
    ∑ u : CoupledCoreIndex N, star (coupledBasisKet s u) * coupledBasisKet t u =
      if s = t then 1 else 0 := by
  by_cases h : s = t
  · subst h
    rw [show (∑ u : CoupledCoreIndex N, star (coupledBasisKet s u) * coupledBasisKet s u) =
        ∑ u : CoupledCoreIndex N, coupledBasisKet s u by
          apply Finset.sum_congr rfl
          intro u hu
          simp [coupledBasisKet]]
    rw [Finset.sum_eq_single s]
    · simp [coupledBasisKet]
    · intro u hu hne
      simp [coupledBasisKet, hne]
    · intro hnot
      exact absurd (Finset.mem_univ s) hnot
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hs : u = s <;> by_cases ht : u = t
    · subst hs; subst ht; contradiction
    · subst hs
      simp [coupledBasisKet, h]
    · subst ht
      simp [coupledBasisKet, hs]
    · simp [coupledBasisKet, hs, ht]

/-- The tensor-Weyl monomial sends a coupled basis ket to a phased shifted basis ket. -/
theorem tensorWeylMonomial_basisKet {N : ℕ} (a b s : CoupledCoreIndex N) :
    tensorWeylMonomial a b (coupledBasisKet s) =
      (phaseCharacter b (addedConfig a s)) • coupledBasisKet (addedConfig a s) := by
  ext t
  by_cases ht : t = addedConfig a s
  · subst ht
    simp [tensorWeylMonomial, coupledBasisKet, shiftedConfig_addedConfig]
  · have hshift : shiftedConfig a t ≠ s := by
      intro hEq
      apply ht
      calc
        t = addedConfig a (shiftedConfig a t) := by symm; exact addedConfig_shiftedConfig a t
        _ = addedConfig a s := by rw [hEq]
    simp [tensorWeylMonomial, coupledBasisKet, hshift, ht]

/-- The local ququart Weyl monomial `X^a Z^b` written directly on the
single-core carrier. -/
def localWeylMonomial (a b : Fin 4) : QuquartState →ₗ[ℂ] QuquartState where
  toFun := fun ψ s => Complex.I ^ (b.val * s.val) * ψ (sub4 s a)
  map_add' := by
    intro ψ χ
    ext s
    simp
    ring
  map_smul' := by
    intro z ψ
    ext s
    simp
    ring

/-- Hilbert-Schmidt-style pairing on single-core operators in the standard
ququart basis. -/
def localOperatorInner (A B : QuquartState →ₗ[ℂ] QuquartState) : ℂ :=
  ∑ s : Fin 4, ∑ t : Fin 4, star (A (basisKet s) t) * B (basisKet s) t

/-- The standard ququart basis is orthonormal for the explicit finite sum. -/
theorem basisKet_orthonormal (m n : Fin 4) :
    ∑ t : Fin 4, star (basisKet m t) * basisKet n t = if m = n then 1 else 0 := by
  fin_cases m <;> fin_cases n <;> simp [basisKet]

/-- Mod-4 subtraction undoes mod-4 addition. -/
theorem sub4_add4_cancel (a s : Fin 4) :
    sub4 (add4 a s) a = s := by
  fin_cases a <;> fin_cases s <;> rfl

/-- Mod-4 addition undoes mod-4 subtraction. -/
theorem add4_sub4_cancel (m a : Fin 4) :
    add4 a (sub4 m a) = m := by
  fin_cases m <;> fin_cases a <;> rfl

/-- The local Weyl monomial sends a basis ket to a phased basis ket. -/
theorem localWeylMonomial_basisKet (a b s : Fin 4) :
    localWeylMonomial a b (basisKet s) =
      (Complex.I ^ (b.val * (add4 a s).val)) • basisKet (add4 a s) := by
  ext m
  by_cases hm : m = add4 a s
  · subst hm
    simp [localWeylMonomial, basisKet, sub4_add4_cancel_core]
  · have hsub : sub4 m a ≠ s := by
      intro hEq
      apply hm
      calc
        m = add4 a (sub4 m a) := by symm; exact add4_sub4_cancel_core m a
        _ = add4 a s := by rw [hEq]
    simp [localWeylMonomial, basisKet, hm, hsub]

/-- For fixed `s`, the shift label `a` is recoverable from `add4 a s`. -/
theorem add4_eq_add4_iff_left (a a' s : Fin 4) :
    add4 a s = add4 a' s ↔ a = a' := by
  exact add4_eq_add4_iff_left_core a a' s

/-- Powers of `i` have unit modulus. -/
lemma I_pow_star_mul_self (n : ℕ) :
    star (Complex.I ^ n) * Complex.I ^ n = 1 := by
  have hnorm : Complex.normSq (Complex.I ^ n) = 1 := by
    simp [Complex.normSq_I]
  have hconj : ((Complex.normSq (Complex.I ^ n) : ℂ) =
      star (Complex.I ^ n) * Complex.I ^ n) := by
    simpa using (Complex.normSq_eq_conj_mul_self (z := Complex.I ^ n))
  rw [hnorm] at hconj
  exact hconj.symm

/-- Powers of `-i` factor through powers of `-1` and `i`. -/
lemma neg_I_pow (n : ℕ) :
    (-Complex.I) ^ n = (-1 : ℂ) ^ n * Complex.I ^ n := by
  rw [show (-Complex.I) = (-1 : ℂ) * Complex.I by ring, mul_pow]

lemma I_pow_five : Complex.I ^ 5 = Complex.I := by
  simpa using (Complex.I_pow_eq_pow_mod 5)

/-- Inner product of two scaled basis kets. -/
lemma scaled_basisKet_inner (c d : ℂ) (m n : Fin 4) :
    ∑ t : Fin 4, star ((c • basisKet m) t) * ((d • basisKet n) t) =
      star c * d * (if m = n then 1 else 0) := by
  calc
    ∑ t : Fin 4, star ((c • basisKet m) t) * ((d • basisKet n) t)
        = ∑ t : Fin 4, star c * d * (star (basisKet m t) * basisKet n t) := by
            apply Finset.sum_congr rfl
            intro t ht
            simp [Pi.smul_apply]
            ring
    _ = star c * d * ∑ t : Fin 4, star (basisKet m t) * basisKet n t := by
          rw [← Finset.mul_sum]
    _ = star c * d * (if m = n then 1 else 0) := by
          rw [basisKet_orthonormal]

/-- Each local Weyl monomial has Hilbert-Schmidt norm squared `4`. -/
theorem localWeylMonomial_self_inner (a b : Fin 4) :
    localOperatorInner (localWeylMonomial a b) (localWeylMonomial a b) = 4 := by
  unfold localOperatorInner
  have hs : ∀ s : Fin 4,
      ∑ t : Fin 4,
        star ((localWeylMonomial a b (basisKet s)) t) *
          (localWeylMonomial a b (basisKet s)) t = 1 := by
    intro s
    have hphase : (-Complex.I) ^ (b.val * (add4 a s).val) *
        Complex.I ^ (b.val * (add4 a s).val) = 1 := by
      simpa using I_pow_star_mul_self (b.val * (add4 a s).val)
    have hinner :=
      scaled_basisKet_inner
        (Complex.I ^ (b.val * (add4 a s).val))
        (Complex.I ^ (b.val * (add4 a s).val))
        (add4 a s) (add4 a s)
    calc
      ∑ t : Fin 4,
          star ((localWeylMonomial a b (basisKet s)) t) *
            (localWeylMonomial a b (basisKet s)) t
          = (-Complex.I) ^ (b.val * (add4 a s).val) *
              Complex.I ^ (b.val * (add4 a s).val) := by
                simpa [localWeylMonomial_basisKet] using hinner
      _ = 1 := hphase
  rw [Fin.sum_univ_four]
  rw [hs 0, hs 1, hs 2, hs 3]
  norm_num

/-- Distinct shift labels force Hilbert-Schmidt orthogonality. -/
theorem localWeylMonomial_shift_orthogonal {a a' : Fin 4} (h : a ≠ a') (b b' : Fin 4) :
    localOperatorInner (localWeylMonomial a b) (localWeylMonomial a' b') = 0 := by
  unfold localOperatorInner
  apply Finset.sum_eq_zero
  intro s hs
  rw [localWeylMonomial_basisKet, localWeylMonomial_basisKet]
  have hidx : add4 a s ≠ add4 a' s := by
    intro hEq
    exact h ((add4_eq_add4_iff_left a a' s).mp hEq)
  have hinner :=
    scaled_basisKet_inner
      (Complex.I ^ (b.val * (add4 a s).val))
      (Complex.I ^ (b'.val * (add4 a' s).val))
      (add4 a s) (add4 a' s)
  simpa [localWeylMonomial_basisKet, hidx] using hinner

set_option maxHeartbeats 800000
/-- Equal shifts but distinct phase labels are orthogonal in the one-core Weyl family. -/
theorem localWeylMonomial_phase_orthogonal (a : Fin 4) {b b' : Fin 4} (h : b ≠ b') :
    localOperatorInner (localWeylMonomial a b) (localWeylMonomial a b') = 0 := by
  unfold localOperatorInner
  have hs : ∀ s : Fin 4,
      ∑ t : Fin 4,
        star ((localWeylMonomial a b (basisKet s)) t) *
          (localWeylMonomial a b' (basisKet s)) t =
        (-Complex.I) ^ (b.val * (add4 a s).val) *
          Complex.I ^ (b'.val * (add4 a s).val) := by
    intro s
    have hinner :=
      scaled_basisKet_inner
        (Complex.I ^ (b.val * (add4 a s).val))
        (Complex.I ^ (b'.val * (add4 a s).val))
        (add4 a s) (add4 a s)
    simpa [localWeylMonomial_basisKet] using hinner
  rw [Fin.sum_univ_four]
  rw [hs 0, hs 1, hs 2, hs 3]
  fin_cases a <;> fin_cases b <;> fin_cases b' <;>
    simp at h <;>
    simp [add4, neg_I_pow, Complex.I_pow_eq_pow_mod] <;>
    ring_nf <;> simp [I_pow_five]
set_option maxHeartbeats 200000

/-- Full local orthogonality for distinct one-core Weyl labels. -/
theorem localWeylMonomial_orthogonal_of_ne {a b a' b' : Fin 4}
    (h : (a, b) ≠ (a', b')) :
    localOperatorInner (localWeylMonomial a b) (localWeylMonomial a' b') = 0 := by
  by_cases ha : a = a'
  · subst ha
    apply localWeylMonomial_phase_orthogonal
    intro hb
    apply h
    simp [hb]
  · exact localWeylMonomial_shift_orthogonal ha b b'

/-- The local Weyl family has the expected cardinality `16`. -/
theorem localWeylFamily_card :
    Fintype.card (Fin 4 × Fin 4) = 16 := by decide

/-- Inner product of two scaled coupled basis kets. -/
lemma scaled_coupledBasisKet_inner {N : ℕ} (c d : ℂ)
    (m n : CoupledCoreIndex N) :
    ∑ t : CoupledCoreIndex N, star ((c • coupledBasisKet m) t) * ((d • coupledBasisKet n) t) =
      star c * d * (if m = n then 1 else 0) := by
  calc
    ∑ t : CoupledCoreIndex N, star ((c • coupledBasisKet m) t) * ((d • coupledBasisKet n) t)
        = ∑ t : CoupledCoreIndex N,
            star c * d * (star (coupledBasisKet m t) * coupledBasisKet n t) := by
              apply Finset.sum_congr rfl
              intro t ht
              simp [Pi.smul_apply]
              ring
    _ = star c * d * ∑ t : CoupledCoreIndex N,
          star (coupledBasisKet m t) * coupledBasisKet n t := by
            rw [← Finset.mul_sum]
    _ = star c * d * (if m = n then 1 else 0) := by
          rw [coupledBasisKet_orthonormal]

/-- Distinct tensor-Weyl displacement labels send the same coupled basis state
to orthogonal outputs. -/
theorem tensorWeylMonomial_basis_image_orthogonal {N : ℕ}
    {a a' : CoupledCoreIndex N} (h : a ≠ a') (b b' : CoupledCoreIndex N)
    (s : CoupledCoreIndex N) :
    ∑ t : CoupledCoreIndex N,
      star ((tensorWeylMonomial a b (coupledBasisKet s)) t) *
        (tensorWeylMonomial a' b' (coupledBasisKet s)) t = 0 := by
  rw [tensorWeylMonomial_basisKet, tensorWeylMonomial_basisKet]
  have hidx : addedConfig a s ≠ addedConfig a' s := by
    intro hEq
    exact h ((addedConfig_eq_addedConfig_iff_left a a' s).mp hEq)
  have hinner :=
    scaled_coupledBasisKet_inner
      (phaseCharacter b (addedConfig a s))
      (phaseCharacter b' (addedConfig a' s))
      (addedConfig a s) (addedConfig a' s)
  simpa [hidx] using hinner

/-- Hilbert-Schmidt-style pairing on coupled-core operators. -/
def coupledOperatorInner {N : ℕ}
    (A B : CoupledCoreSpace N →ₗ[ℂ] CoupledCoreSpace N) : ℂ :=
  ∑ s : CoupledCoreIndex N, ∑ t : CoupledCoreIndex N,
    star (A (coupledBasisKet s) t) * B (coupledBasisKet s) t

/-- The coupled phase character has unit modulus. -/
lemma phaseCharacter_star_mul_self {N : ℕ} (b s : CoupledCoreIndex N) :
    star (phaseCharacter b s) * phaseCharacter b s = 1 := by
  have hnorm : Complex.normSq (phaseCharacter b s) = 1 := by
    unfold phaseCharacter
    rw [map_prod Complex.normSq]
    apply Finset.prod_eq_one
    intro x hx
    simp [Complex.normSq_I]
  have hconj := Complex.normSq_eq_conj_mul_self (z := phaseCharacter b s)
  rw [hnorm] at hconj
  exact hconj.symm

/-- A tensor-Weyl monomial has Hilbert-Schmidt norm squared equal to the
dimension of the coupled-core carrier. -/
theorem tensorWeylMonomial_self_inner {N : ℕ} (a b : CoupledCoreIndex N) :
    coupledOperatorInner (tensorWeylMonomial a b) (tensorWeylMonomial a b) =
      Fintype.card (CoupledCoreIndex N) := by
  unfold coupledOperatorInner
  have hs : ∀ s : CoupledCoreIndex N,
      ∑ t : CoupledCoreIndex N,
        star ((tensorWeylMonomial a b (coupledBasisKet s)) t) *
          (tensorWeylMonomial a b (coupledBasisKet s)) t = 1 := by
    intro s
    let c := phaseCharacter b (addedConfig a s)
    let m := addedConfig a s
    have hinner := scaled_coupledBasisKet_inner c c m m
    rw [if_pos rfl, mul_one] at hinner
    calc
      ∑ t : CoupledCoreIndex N,
          star ((tensorWeylMonomial a b (coupledBasisKet s)) t) *
            (tensorWeylMonomial a b (coupledBasisKet s)) t
        = ∑ t : CoupledCoreIndex N,
            star ((c • coupledBasisKet m) t) * ((c • coupledBasisKet m) t) := by
              rw [tensorWeylMonomial_basisKet]
      _ = star c * c := hinner
      _ = 1 := phaseCharacter_star_mul_self b (addedConfig a s)
  calc
    ∑ s : CoupledCoreIndex N, ∑ t : CoupledCoreIndex N,
        star ((tensorWeylMonomial a b (coupledBasisKet s)) t) *
          (tensorWeylMonomial a b (coupledBasisKet s)) t
      = ∑ _s : CoupledCoreIndex N, (1 : ℂ) := by
          apply Finset.sum_congr rfl; intro s _; exact hs s
    _ = Fintype.card (CoupledCoreIndex N) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Distinct coupled tensor-Weyl displacement labels are orthogonal in the
Hilbert-Schmidt pairing. -/
theorem tensorWeylMonomial_shift_orthogonal {N : ℕ}
    {a a' : CoupledCoreIndex N} (h : a ≠ a') (b b' : CoupledCoreIndex N) :
    coupledOperatorInner (tensorWeylMonomial a b) (tensorWeylMonomial a' b') = 0 := by
  unfold coupledOperatorInner
  apply Finset.sum_eq_zero
  intro s hs
  exact tensorWeylMonomial_basis_image_orthogonal h b b' s

/-- Enumeration of the coupled-core basis by a finite index. -/
def coupledCoreEquivFin (N : ℕ) :
    CoupledCoreIndex N ≃ Fin (Fintype.card (CoupledCoreIndex N)) :=
  Fintype.equivFin (CoupledCoreIndex N)

/-- Zero-pad a finite-dimensional state into a coupled-core carrier. -/
def embedState {d N : ℕ} (_h : d ≤ Fintype.card (CoupledCoreIndex N)) :
    (Fin d → ℂ) →ₗ[ℂ] CoupledCoreSpace N where
  toFun := fun v s =>
    let i := coupledCoreEquivFin N s
    if hi : i.val < d then v ⟨i.val, hi⟩ else 0
  map_add' := by
    intro v w
    ext s
    dsimp [coupledCoreEquivFin]
    split_ifs <;> simp
  map_smul' := by
    intro z v
    ext s
    dsimp [coupledCoreEquivFin]
    split_ifs <;> simp

/-- Restrict a coupled-core state back to the first `d` coordinates of the
enumerated basis. -/
def projectState {d N : ℕ} (h : d ≤ Fintype.card (CoupledCoreIndex N)) :
    CoupledCoreSpace N →ₗ[ℂ] (Fin d → ℂ) where
  toFun := fun ψ i => ψ ((coupledCoreEquivFin N).symm (Fin.castLE h i))
  map_add' := by
    intro ψ χ
    ext i
    rfl
  map_smul' := by
    intro z ψ
    ext i
    rfl

/-- Projection recovers the original state after zero-padding. -/
theorem projectState_embedState {d N : ℕ} (h : d ≤ Fintype.card (CoupledCoreIndex N))
    (v : Fin d → ℂ) :
    projectState h (embedState h v) = v := by
  ext i
  unfold projectState embedState
  simp [coupledCoreEquivFin]

/-- Zero-padding is injective. -/
theorem embedState_injective {d N : ℕ} (h : d ≤ Fintype.card (CoupledCoreIndex N)) :
    Function.Injective (embedState h) := by
  intro v w hEq
  have hproj := congrArg (projectState h) hEq
  simpa [projectState_embedState] using hproj

/-- Lift a finite-dimensional linear operator to the coupled-core carrier by
zero-padding, acting, and projecting back. -/
def liftOperator {d N : ℕ} (h : d ≤ Fintype.card (CoupledCoreIndex N))
    (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    CoupledCoreSpace N →ₗ[ℂ] CoupledCoreSpace N :=
  (embedState h).comp (T.comp (projectState h))

/-- The lifted operator acts exactly like the original operator on the embedded
subspace. -/
theorem liftOperator_intertwines {d N : ℕ} (h : d ≤ Fintype.card (CoupledCoreIndex N))
    (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) (v : Fin d → ℂ) :
    liftOperator h T (embedState h v) = embedState h (T v) := by
  unfold liftOperator
  simp [projectState_embedState]

/-- The obvious capacity bound: `d ≤ 4^d`. -/
theorem self_le_four_pow_self : ∀ d : ℕ, d ≤ 4 ^ d
  | 0 => by norm_num
  | d + 1 =>
      let m := 4 ^ d
      have hm : d ≤ m := self_le_four_pow_self d
      have hm_pos : 1 ≤ m := by
        dsimp [m]
        exact Nat.succ_le_of_lt (pow_pos (by norm_num) _)
      have hstep : d + 1 ≤ m + m := by
        omega
      calc
        d + 1 ≤ m + m := hstep
        _ ≤ 4 * m := by omega
        _ = 4 ^ (d + 1) := by
              dsimp [m]
              rw [pow_succ]
              ring

/-- Any finite-dimensional linear dynamics embeds exactly into a coupled-core
carrier with enough ququart capacity. Here we use `N = d`, since `d ≤ 4^d`. -/
theorem finite_dimensional_exact_embedding (d : ℕ)
    (T : (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ)) :
    ∃ L : CoupledCoreSpace d →ₗ[ℂ] CoupledCoreSpace d,
      ∀ v : Fin d → ℂ,
        L (embedState (N := d) (by simpa [coupledCoreIndex_card] using self_le_four_pow_self d) v) =
          embedState (N := d) (by simpa [coupledCoreIndex_card] using self_le_four_pow_self d) (T v) := by
  let hcap : d ≤ Fintype.card (CoupledCoreIndex d) := by
    simpa [coupledCoreIndex_card] using self_le_four_pow_self d
  refine ⟨liftOperator (N := d) hcap T, ?_⟩
  intro v
  exact liftOperator_intertwines (N := d) hcap T v

end

end CoupledRecognitionCores
end Foundation
end IndisputableMonolith
