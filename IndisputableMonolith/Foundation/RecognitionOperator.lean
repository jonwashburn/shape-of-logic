import IndisputableMonolith.Foundation.ComplexStructureForcing

open scoped BigOperators

namespace IndisputableMonolith
namespace Foundation

open ComplexStructureForcing
open IndisputableMonolith.Spectral

noncomputable section

abbrev Signal8 := ComplexStructureForcing.Signal8

/-! ## Legacy ledger compatibility surface

Several older bridge modules were written against a ledger-side
`RecognitionOperator` API with fields such as `LedgerState.time`,
`LedgerState.Z_patterns`, and `RecognitionCost`. The current canonical
operator in this file is the analytic 8-tick operator on `Signal8`.

To keep those older bridge modules buildable without reintroducing the
retired ledger implementation, we expose a minimal compatibility surface:
`LedgerState` is the analytic signal carrier, and the old ledger projections
are harmless readout functions. This does not change the spectral operator
content below; it only prevents stale bridge files from breaking the main
foundation imports.
-/

abbrev BondId := ℕ
abbrev AgentId := ℕ
abbrev LedgerState := Signal8

namespace LedgerState

def time (_s : LedgerState) : ℕ := 0
def Z_patterns (_s : LedgerState) : List ℤ := []
def global_phase (_s : LedgerState) : ℝ := 0
def channels (_s : LedgerState) : List ℕ := []
def active_bonds (_s : LedgerState) : Finset BondId := ∅
def bond_multipliers (_s : LedgerState) (_b : BondId) : ℝ := 1
def bond_pos (s : LedgerState) {b : BondId} (_hb : b ∈ active_bonds s) :
    0 < bond_multipliers s b := by
  simp [bond_multipliers]
def bond_agents (_s : LedgerState) (_b : BondId) : AgentId × AgentId := (0, 0)

end LedgerState

def total_Z (_s : LedgerState) : ℤ := 0
def RecognitionCost (_s : LedgerState) : ℝ := 0
def net_skew (_s : LedgerState) : ℝ := 0
def signed_log_flow (_s : LedgerState) (_b : BondId) : ℝ := 0
def reciprocity_skew (_s : LedgerState) (_b : BondId) : ℝ := 0
def reciprocity_skew_abs (_s : LedgerState) : ℝ := 0
def admissible (_s : LedgerState) : Prop := True

/-- The neutral register is the mean-free subspace of the 8-tick carrier. -/
def neutralRegister : Submodule ℂ Signal8 where
  carrier := {f | Finset.univ.sum f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change Finset.univ.sum (f + g) = 0
    simpa [Pi.add_apply, Finset.sum_add_distrib] using
      congrArg₂ (fun x y : ℂ => x + y) hf hg
  smul_mem' := by
    intro a f hf
    change Finset.univ.sum (a • f) = 0
    simpa [Pi.smul_apply, Finset.mul_sum] using
      congrArg (fun x : ℂ => a * x) hf

/-- The quarter-turn core is the span of the odd DFT modes. -/
def quarterTurnCore : Submodule ℂ Signal8 :=
  Submodule.span ℂ {m | ∃ k : Fin 8, Odd k.val ∧ m = dft8_mode k}

/-- A structured sector extends the quarter-turn core by adding
selected non-DC modes. -/
structure StructuredSector where
  keepModes : Finset (Fin 8)
  odd_modes_included : ∀ {k : Fin 8}, Odd k.val → k ∈ keepModes
  dc_mode_excluded : (0 : Fin 8) ∉ keepModes

/-- The canonical odd-mode index set `{1,3,5,7}`. -/
def quarterTurnModes : Finset (Fin 8) := {1, 3, 5, 7}

/-- Membership in the canonical quarter-turn mode set is exactly odd parity. -/
lemma mem_quarterTurnModes (k : Fin 8) :
    k ∈ quarterTurnModes ↔ Odd k.val := by
  fin_cases k <;> decide

/-- The minimal structured sector used in the paper: keep exactly the odd modes. -/
def quarterTurnSector : StructuredSector where
  keepModes := quarterTurnModes
  odd_modes_included := by
    intro k hk
    simpa [mem_quarterTurnModes] using hk
  dc_mode_excluded := by
    simp [quarterTurnModes]

/-- A public operator record for the projector-followed-by-shift update. -/
structure RecognitionOperator where
  sector : StructuredSector

/-- The bare one-tick propagation operator on `Signal8`. -/
def shiftLinear : Signal8 →ₗ[ℂ] Signal8 where
  toFun := cyclic_shift
  map_add' := by
    intro f g
    ext t
    simp [cyclic_shift]
  map_smul' := by
    intro a f
    ext t
    simp [cyclic_shift]

@[simp] lemma shiftLinear_apply (f : Signal8) :
    shiftLinear f = cyclic_shift f := rfl

/-- The Fourier coefficient map is linear in the signal. -/
lemma dft_coefficients_add (f g : Signal8) (k : Fin 8) :
    dft_coefficients (f + g) k = dft_coefficients f k + dft_coefficients g k := by
  unfold dft_coefficients
  simp [mul_add, Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]

/-- The Fourier coefficient map is linear in the signal. -/
lemma dft_coefficients_smul (a : ℂ) (f : Signal8) (k : Fin 8) :
    dft_coefficients (a • f) k = a * dft_coefficients f k := by
  unfold dft_coefficients
  simp [Pi.smul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- The DFT coefficients of a mode vector are Kronecker-delta normalized. -/
lemma dft_coefficients_mode (j k : Fin 8) :
    dft_coefficients (dft8_mode j) k = if k = j then 1 else 0 := by
  unfold dft_coefficients dft8_mode
  exact dft8_column_orthonormal k j

/-- Each non-DC DFT mode lies in the neutral register. -/
lemma dft8_mode_mem_neutralRegister {k : Fin 8} (hk : k ≠ 0) :
    dft8_mode k ∈ neutralRegister := by
  change Finset.univ.sum (fun t : Fin 8 => dft8_entry t k) = 0
  unfold dft8_entry
  simp_rw [div_eq_mul_inv]
  have hroots :
      Finset.univ.sum (fun t : Fin 8 => omega8 ^ (t.val * k.val)) = 0 :=
    roots_of_unity_sum k hk
  simpa [Finset.sum_mul] using congrArg
    (fun z : ℂ => z * (((Real.sqrt 8 : ℝ) : ℂ)⁻¹)) hroots

/-- The odd Fourier span sits inside the neutral register. -/
theorem quarterTurnCore_le_neutralRegister :
    quarterTurnCore ≤ neutralRegister := by
  refine Submodule.span_le.2 ?_
  intro m hm
  rcases hm with ⟨k, hkodd, rfl⟩
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hkval : k.val = 0 := by simpa using congrArg Fin.val hk0
    have : Odd (0 : ℕ) := by simpa [hkval] using hkodd
    simpa using this
  exact dft8_mode_mem_neutralRegister hk_ne

/-- The canonical projector onto a structured sector keeps exactly the chosen
Fourier modes. -/
def sectorProject (S : StructuredSector) : Signal8 →ₗ[ℂ] Signal8 where
  toFun := fun f => fun t => Finset.sum S.keepModes (fun k => dft_coefficients f k * dft8_entry t k)
  map_add' := by
    intro f g
    ext t
    calc
      Finset.sum S.keepModes (fun k => dft_coefficients (f + g) k * dft8_entry t k)
          = Finset.sum S.keepModes (fun k => (dft_coefficients f k + dft_coefficients g k) * dft8_entry t k) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [dft_coefficients_add]
      _ = Finset.sum S.keepModes (fun k => dft_coefficients f k * dft8_entry t k +
            dft_coefficients g k * dft8_entry t k) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = Finset.sum S.keepModes (fun k => dft_coefficients f k * dft8_entry t k) +
            Finset.sum S.keepModes (fun k => dft_coefficients g k * dft8_entry t k) := by
              rw [Finset.sum_add_distrib]
  map_smul' := by
    intro a f
    ext t
    calc
      Finset.sum S.keepModes (fun k => dft_coefficients (a • f) k * dft8_entry t k)
          = Finset.sum S.keepModes (fun k => (a * dft_coefficients f k) * dft8_entry t k) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [dft_coefficients_smul]
      _ = Finset.sum S.keepModes (fun k => a * (dft_coefficients f k * dft8_entry t k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = a * Finset.sum S.keepModes (fun k => dft_coefficients f k * dft8_entry t k) := by
              rw [Finset.mul_sum]

@[simp] lemma sectorProject_apply (S : StructuredSector) (f : Signal8) (t : Fin 8) :
    sectorProject S f t = Finset.sum S.keepModes (fun k => dft_coefficients f k * dft8_entry t k) := rfl

/-- Projecting a basis mode either keeps it or kills it. -/
lemma sectorProject_mode (S : StructuredSector) (k : Fin 8) :
    sectorProject S (dft8_mode k) = if k ∈ S.keepModes then dft8_mode k else 0 := by
  ext t
  by_cases hk : k ∈ S.keepModes
  · rw [if_pos hk, sectorProject_apply]
    rw [Finset.sum_eq_single k]
    · simp [dft_coefficients_mode, dft8_mode, hk]
    · intro j hj hne
      simp [dft_coefficients_mode, hne, dft8_mode]
    · intro hnot
      exact (hnot hk).elim
  · rw [if_neg hk, sectorProject_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hj_ne : j ≠ k := by
      intro hj_eq
      apply hk
      simpa [hj_eq] using hj
    simp [dft_coefficients_mode, hj_ne, dft8_mode]

/-- The concrete recognition update is projector-after-shift. -/
def recognitionUpdate (S : StructuredSector) : Signal8 →ₗ[ℂ] Signal8 :=
  (sectorProject S).comp shiftLinear

@[simp] lemma recognitionUpdate_apply (S : StructuredSector) (f : Signal8) :
    recognitionUpdate S f = sectorProject S (cyclic_shift f) := rfl

/-- The bundled operator evolves by the structured projector update. -/
def RecognitionOperator.evolve (R : RecognitionOperator) : Signal8 →ₗ[ℂ] Signal8 :=
  recognitionUpdate R.sector

/-- Legacy compatibility: analytic evolution preserves admissibility. -/
theorem RecognitionOperator.conserves (R : RecognitionOperator) (s : LedgerState)
    (_hs : admissible s) : admissible (R.evolve s) := by
  trivial

/-- Legacy compatibility: analytic evolution does not increase the placeholder
recognition cost. -/
theorem RecognitionOperator.minimizes_J (R : RecognitionOperator) (s : LedgerState)
    (_hs : admissible s) : RecognitionCost (R.evolve s) ≤ RecognitionCost s := by
  simp [RecognitionCost]

/-- Legacy compatibility: analytic evolution has a (zero) global phase
increment in the placeholder ledger readout. -/
theorem RecognitionOperator.phase_coupling (R : RecognitionOperator) (s : LedgerState) :
    ∃ dTheta : ℝ,
      LedgerState.global_phase (R.evolve s) = LedgerState.global_phase s + dTheta := by
  exact ⟨0, by simp [LedgerState.global_phase]⟩

/-- Iterated cyclic shift. -/
def cyclicShiftIter : ℕ → Signal8 → Signal8
  | 0 => id
  | n + 1 => cyclic_shift ∘ cyclicShiftIter n

/-- Iterated shift preserves addition. -/
lemma cyclicShiftIter_add (n : ℕ) (f g : Signal8) :
    cyclicShiftIter n (f + g) = cyclicShiftIter n f + cyclicShiftIter n g := by
  induction n with
  | zero =>
      ext t
      simp [cyclicShiftIter]
  | succ n ih =>
      ext t
      simp [cyclicShiftIter, ih, cyclic_shift]

/-- Iterated shift commutes with scalar multiplication. -/
lemma cyclicShiftIter_smul (n : ℕ) (a : ℂ) (f : Signal8) :
    cyclicShiftIter n (a • f) = a • cyclicShiftIter n f := by
  induction n with
  | zero =>
      ext t
      simp [cyclicShiftIter]
  | succ n ih =>
      ext t
      simp [cyclicShiftIter, ih, cyclic_shift]

/-- Every DFT mode is an eigenvector of each iterate of the shift. -/
lemma cyclicShiftIter_mode (n : ℕ) (k : Fin 8) :
    cyclicShiftIter n (dft8_mode k) = (omega8 ^ k.val) ^ n • dft8_mode k := by
  induction n with
  | zero =>
      ext t
      simp [cyclicShiftIter]
  | succ n ih =>
      calc
        cyclicShiftIter (n + 1) (dft8_mode k)
            = cyclic_shift (cyclicShiftIter n (dft8_mode k)) := rfl
        _ = cyclic_shift ((omega8 ^ k.val) ^ n • dft8_mode k) := by rw [ih]
        _ = (omega8 ^ k.val) ^ n • cyclic_shift (dft8_mode k) := by
              ext t
              simp [cyclic_shift]
        _ = (omega8 ^ k.val) ^ n • ((omega8 ^ k.val) • dft8_mode k) := by
              rw [dft8_shift_eigenvector]
        _ = (omega8 ^ k.val) ^ (n + 1) • dft8_mode k := by
              ext t
              simp [pow_succ, mul_assoc]

/-- On odd modes, four shifts act by `-1`. -/
lemma odd_mode_fourth_eigenvalue (k : Fin 8) (hk : Odd k.val) :
    (omega8 ^ k.val) ^ 4 = (-1 : ℂ) := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, omega8_pow_4]
  simpa using hk.neg_one_pow

/-- The odd-mode span is invariant under one-tick propagation. -/
theorem shift_mem_quarterTurnCore {f : Signal8} (hf : f ∈ quarterTurnCore) :
    cyclic_shift f ∈ quarterTurnCore := by
  change shiftLinear f ∈ quarterTurnCore
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro m hm
    rcases hm with ⟨k, hkodd, rfl⟩
    rw [shiftLinear_apply, dft8_shift_eigenvector]
    exact Submodule.smul_mem quarterTurnCore _ (Submodule.subset_span ⟨k, hkodd, rfl⟩)
  · change shiftLinear (0 : Signal8) ∈ quarterTurnCore
    rw [map_zero]
    exact quarterTurnCore.zero_mem
  · intro x y hx hy hpx hpy
    change shiftLinear (x + y) ∈ quarterTurnCore
    rw [map_add]
    exact quarterTurnCore.add_mem hpx hpy
  · intro a x hx hpx
    change shiftLinear (a • x) ∈ quarterTurnCore
    rw [map_smul]
    exact quarterTurnCore.smul_mem a hpx

/-- Four shifts act as `-I` on the quarter-turn core. This is the concrete
`P^4 = -I` statement used in the paper. -/
theorem shift_four_eq_neg_on_quarterTurnCore {f : Signal8} (hf : f ∈ quarterTurnCore) :
    cyclicShiftIter 4 f = -f := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro m hm
    rcases hm with ⟨k, hkodd, rfl⟩
    rw [cyclicShiftIter_mode, odd_mode_fourth_eigenvalue k hkodd]
    ext t
    simp
  · ext t
    simp [cyclicShiftIter, cyclic_shift]
  · intro x y hx hy hpx hpy
    calc
      cyclicShiftIter 4 (x + y) = cyclicShiftIter 4 x + cyclicShiftIter 4 y := cyclicShiftIter_add 4 x y
      _ = -x + -y := by rw [hpx, hpy]
      _ = (-1 : ℂ) • x + (-1 : ℂ) • y := by simp
      _ = (-1 : ℂ) • (x + y) := by rw [smul_add]
      _ = -(x + y) := by
            ext t
            simp [smul_eq_mul]
  · intro a x hx hpx
    calc
      cyclicShiftIter 4 (a • x) = a • cyclicShiftIter 4 x := cyclicShiftIter_smul 4 a x
      _ = a • (-x) := by rw [hpx]
      _ = -(a • x) := by simp

/-- Two beats square to `-I` on the quarter-turn core. -/
theorem twoBeat_square_eq_neg_on_quarterTurnCore {f : Signal8} (hf : f ∈ quarterTurnCore) :
    cyclicShiftIter 2 (cyclicShiftIter 2 f) = -f := by
  simpa [cyclicShiftIter] using shift_four_eq_neg_on_quarterTurnCore hf

/-- Every structured-sector projector fixes the quarter-turn core pointwise. -/
theorem sectorProject_eq_id_on_quarterTurnCore (S : StructuredSector) :
    ∀ {f : Signal8}, f ∈ quarterTurnCore → sectorProject S f = f := by
  intro f hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro m hm
    rcases hm with ⟨k, hkodd, rfl⟩
    have hk : k ∈ S.keepModes := S.odd_modes_included hkodd
    simpa [sectorProject_mode, hk] using sectorProject_mode S k
  · exact map_zero (sectorProject S)
  · intro x y hx hy hpx hpy
    calc
      sectorProject S (x + y) = sectorProject S x + sectorProject S y := by
        exact map_add (sectorProject S) x y
      _ = x + y := by rw [hpx, hpy]
  · intro a x hx hpx
    calc
      sectorProject S (a • x) = a • sectorProject S x := by
        exact map_smul (sectorProject S) a x
      _ = a • x := by rw [hpx]

/-- The projector-after-shift update reduces to the bare shift on the
quarter-turn core, independently of the chosen sector extension. -/
theorem recognitionUpdate_eq_shift_on_quarterTurnCore
    (S : StructuredSector) {f : Signal8} (hf : f ∈ quarterTurnCore) :
    recognitionUpdate S f = cyclic_shift f := by
  unfold recognitionUpdate
  exact sectorProject_eq_id_on_quarterTurnCore S (shift_mem_quarterTurnCore hf)

/-- The bundled operator is exactly unitary on the quarter-turn core because
its update collapses to the bare 8-tick shift there. -/
theorem RecognitionOperator.evolve_eq_shift_on_quarterTurnCore
    (R : RecognitionOperator) {f : Signal8} (hf : f ∈ quarterTurnCore) :
    R.evolve f = cyclic_shift f :=
  recognitionUpdate_eq_shift_on_quarterTurnCore R.sector hf

end

end Foundation
end IndisputableMonolith
