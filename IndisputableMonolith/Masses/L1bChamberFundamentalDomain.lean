import Mathlib
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup
import IndisputableMonolith.Masses.L1bSignedActMeasure
import IndisputableMonolith.Masses.L1bChamberMeasure

/-!
# L1b chamber fundamental domain

The hyperoctahedral group `SignedPerm` (order 48) acts linearly on `ℝ³` by
permuting coordinates and flipping signs (`signedAct`). This file proves that the
open positive sorted cone

  `cone = {v | 0 < v 0 ∧ v 0 < v 1 ∧ v 1 < v 2}`

is a fundamental domain for that action with respect to Lebesgue `volume`. Together
with `L1bChamberMeasure.tile_measure_of_card48` (one invariant set is `48 ×` its
intersection with the tile) this is the geometric link that ties the finite `1/48`
to the boundary `1/(4π)`.

Strategy for `IsFundamentalDomain.mk`:
* `nullMeasurableSet`: the cone is open (intersection of three open half-spaces).
* `aedisjoint`: in fact *exactly* disjoint. A point of the cone has strictly
  increasing, strictly positive coordinates, so the only group element fixing the
  sorted-positive chamber is the identity (`cone_smul_eq_one`).
* `ae_covers`: the complement of the cover lies in a finite union of coordinate
  hyperplanes `{v i = 0}` and `{|v i| = |v j|}`, each a proper linear subspace,
  hence Lebesgue-null (`Measure.addHaar_submodule`). Off that null set the
  coordinates have distinct nonzero absolute values, so sorting `|v|` and choosing
  signs to make every coordinate positive maps `v` into the cone.
-/

namespace IndisputableMonolith.Masses.L1bChamberFundamentalDomain

open MeasureTheory
open scoped Pointwise
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup.SignedPerm
open IndisputableMonolith.Masses.L1bSignedActMeasure

abbrev V := Fin 3 → ℝ

/-- Discrete σ-algebra on the finite group. -/
instance : MeasurableSpace SignedPerm := ⊤

/-- Lebesgue volume on `ℝ³` is invariant under the signed-permutation action. -/
instance : SMulInvariantMeasure SignedPerm V (volume : Measure V) where
  measure_preimage_smul c s hs :=
    (measurePreserving_signedAct c).measure_preimage hs.nullMeasurableSet

instance : MeasurableSMul SignedPerm V where
  measurable_const_smul c := (measurePreserving_signedAct c).measurable
  measurable_smul_const _ := measurable_from_top

/-- The open positive sorted chamber. -/
def cone : Set V := {v | 0 < v 0 ∧ v 0 < v 1 ∧ v 1 < v 2}

theorem cone_open : IsOpen cone := by
  have h0 : IsOpen {v : V | 0 < v 0} := isOpen_lt continuous_const (continuous_apply 0)
  have h1 : IsOpen {v : V | v 0 < v 1} := isOpen_lt (continuous_apply 0) (continuous_apply 1)
  have h2 : IsOpen {v : V | v 1 < v 2} := isOpen_lt (continuous_apply 1) (continuous_apply 2)
  have heq : cone = {v : V | 0 < v 0} ∩ {v : V | v 0 < v 1} ∩ {v : V | v 1 < v 2} := by
    ext v; constructor
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, b⟩, c⟩
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, b, c⟩
  rw [heq]; exact (h0.inter h1).inter h2

theorem cone_nullMeasurable : NullMeasurableSet cone (volume : Measure V) :=
  cone_open.nullMeasurableSet

/-- Every coordinate of a cone point is strictly positive. -/
theorem cone_pos {a : V} (ha : a ∈ cone) : ∀ j, 0 < a j := by
  obtain ⟨h0, h1, h2⟩ := ha
  intro j
  fin_cases j
  · exact h0
  · exact lt_trans h0 h1
  · exact lt_trans (lt_trans h0 h1) h2

/-- A cone point is a strictly monotone function `Fin 3 → ℝ`. -/
theorem cone_strictMono {a : V} (ha : a ∈ cone) : StrictMono a := by
  obtain ⟨h0, h1, h2⟩ := ha
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · simpa using h1
  · simpa using h2

/-! ### The key chamber-uniqueness lemma -/

/-- If `a` and `k • a` both lie in the cone, then `k = 1`. The cone forces all
coordinates positive (so every sign bit is `false`) and strictly increasing (so the
permutation, sending an increasing sequence to an increasing sequence, is the
identity). -/
theorem cone_smul_eq_one {k : SignedPerm} {a : V}
    (ha : a ∈ cone) (hka : k • a ∈ cone) : k = 1 := by
  have hapos := cone_pos ha
  -- Step 1: every sign bit is false (else some coordinate would be negative).
  have hsign : ∀ i, k.sign i = false := by
    intro i
    by_contra hne
    have htrue : k.sign i = true := by
      cases h : k.sign i with
      | false => exact absurd h hne
      | true => rfl
    have heval : signedAct k a i = -(a (k.perm i)) := by
      simp [signedAct, htrue]
    have hki : 0 < (k • a) i := cone_pos hka i
    rw [smul_def, heval] at hki
    linarith [hapos (k.perm i)]
  -- Step 2: with all signs false, the action is pure coordinate permutation.
  have hval : ∀ i, (k • a) i = a (k.perm i) := by
    intro i
    rw [smul_def]
    simp [signedAct, hsign i]
  obtain ⟨_, hk01, hk12⟩ := hka
  rw [hval, hval] at hk01
  rw [hval, hval] at hk12
  have ha_mono := cone_strictMono ha
  have hp01 : k.perm 0 < k.perm 1 := ha_mono.lt_iff_lt.mp hk01
  have hp12 : k.perm 1 < k.perm 2 := ha_mono.lt_iff_lt.mp hk12
  -- Step 3: the only permutation of `Fin 3` with `σ0 < σ1 < σ2` is the identity.
  have hperm : k.perm = 1 := by
    have hdec : ∀ σ : Equiv.Perm (Fin 3), σ 0 < σ 1 → σ 1 < σ 2 → σ = 1 := by decide
    exact hdec k.perm hp01 hp12
  refine SignedPerm.ext ?_ ?_
  · rw [one_perm]; exact hperm
  · funext i; rw [one_sign]; exact hsign i

/-! ### a.e. disjointness -/

theorem cone_disjoint {g h : SignedPerm} (hgh : g ≠ h) :
    Disjoint (g • cone) (h • cone) := by
  rw [Set.disjoint_left]
  intro v hvg hvh
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hvg hvh
  -- `g⁻¹ • v ∈ cone` and `h⁻¹ • v ∈ cone`; relate them by `k = h⁻¹ * g`.
  have hkey : (h⁻¹ * g) • (g⁻¹ • v) ∈ cone := by
    have hrw : (h⁻¹ * g) • (g⁻¹ • v) = h⁻¹ • v := by
      rw [mul_smul, smul_inv_smul]
    rw [hrw]; exact hvh
  have hk1 : (h⁻¹ * g) = 1 := cone_smul_eq_one hvg hkey
  exact hgh ((inv_mul_eq_one.mp hk1).symm)

/-! ### Null bad set -/

/-- Any nonzero linear functional has a null zero locus (its kernel is a proper
subspace, hence Lebesgue-null). -/
theorem ker_null (L : V →ₗ[ℝ] ℝ) (hL : L ≠ 0) :
    (volume : Measure V) {v | L v = 0} = 0 := by
  have htop : LinearMap.ker L ≠ ⊤ := by
    rw [Ne, LinearMap.ker_eq_top]; exact hL
  have h := Measure.addHaar_submodule (volume : Measure V) (LinearMap.ker L) htop
  have hset : (↑(LinearMap.ker L) : Set V) = {v | L v = 0} := by
    ext v; simp [LinearMap.mem_ker]
  rwa [hset] at h

theorem coord_null (i : Fin 3) : (volume : Measure V) {v : V | v i = 0} = 0 := by
  refine ker_null (LinearMap.proj i) ?_
  intro hL
  have := LinearMap.congr_fun hL (Pi.single i 1)
  simp [LinearMap.proj_apply, Pi.single_eq_same] at this

theorem eq_null {i j : Fin 3} (hij : i ≠ j) :
    (volume : Measure V) {v : V | v i = v j} = 0 := by
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun w => w i - w j
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hLne : L ≠ 0 := by
    intro hL
    have hc : (Pi.single i (1 : ℝ) : V) i - (Pi.single i (1 : ℝ) : V) j = 0 :=
      LinearMap.congr_fun hL (Pi.single i 1)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hc
    norm_num at hc
  have hk := ker_null L hLne
  have hset : {v : V | v i = v j} = {v : V | L v = 0} := by
    ext v
    constructor
    · intro (h : v i = v j); show v i - v j = 0; rw [h, sub_self]
    · intro (h : v i - v j = 0); show v i = v j; linarith
  rw [hset]; exact hk

theorem negeq_null {i j : Fin 3} (hij : i ≠ j) :
    (volume : Measure V) {v : V | v i = -v j} = 0 := by
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun w => w i + w j
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hLne : L ≠ 0 := by
    intro hL
    have hc : (Pi.single i (1 : ℝ) : V) i + (Pi.single i (1 : ℝ) : V) j = 0 :=
      LinearMap.congr_fun hL (Pi.single i 1)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at hc
    norm_num at hc
  have hk := ker_null L hLne
  have hset : {v : V | v i = -v j} = {v : V | L v = 0} := by
    ext v
    constructor
    · intro (h : v i = -v j); show v i + v j = 0; rw [h]; ring
    · intro (h : v i + v j = 0); show v i = -v j; linarith
  rw [hset]; exact hk

/-- The bad set: some coordinate vanishes, or two coordinates share absolute value. -/
def badSet : Set V := {v | (∃ i, v i = 0) ∨ (∃ i j, i ≠ j ∧ |v i| = |v j|)}

theorem badSet_null : (volume : Measure V) badSet = 0 := by
  have hzero : (volume : Measure V) {v : V | ∃ i, v i = 0} = 0 := by
    rw [Set.setOf_exists]
    exact measure_iUnion_null (fun i => coord_null i)
  have habs : (volume : Measure V) {v : V | ∃ i j, i ≠ j ∧ |v i| = |v j|} = 0 := by
    rw [Set.setOf_exists]
    refine measure_iUnion_null (fun i => ?_)
    rw [Set.setOf_exists]
    refine measure_iUnion_null (fun j => ?_)
    by_cases hij : i = j
    · have hempty : {v : V | i ≠ j ∧ |v i| = |v j|} = (∅ : Set V) := by
        ext v; simp [hij]
      rw [hempty, measure_empty]
    · have hsub : {v : V | i ≠ j ∧ |v i| = |v j|}
          ⊆ {v : V | v i = v j} ∪ {v : V | v i = -v j} := by
        intro v hv
        rcases abs_eq_abs.mp hv.2 with h | h
        · exact Or.inl h
        · exact Or.inr h
      exact measure_mono_null hsub (measure_union_null (eq_null hij) (negeq_null hij))
  have hsplit : badSet
      = {v : V | ∃ i, v i = 0} ∪ {v : V | ∃ i j, i ≠ j ∧ |v i| = |v j|} := rfl
  rw [hsplit]
  exact measure_union_null hzero habs

/-! ### a.e. coverage -/

/-- Off the bad set, sorting `|v|` and orienting all coordinates positive maps `v`
into the cone. -/
theorem exists_mem_cone_of_not_bad {v : V} (hv : v ∉ badSet) :
    ∃ g : SignedPerm, g • v ∈ cone := by
  have hraw : ¬ ((∃ i, v i = 0) ∨ (∃ i j, i ≠ j ∧ |v i| = |v j|)) := hv
  push_neg at hraw
  obtain ⟨hnz, hdist⟩ := hraw
  -- `hnz : ∀ i, v i ≠ 0`, `hdist : ∀ i j, i ≠ j → |v i| ≠ |v j|`.
  set σ : Equiv.Perm (Fin 3) := Tuple.sort (fun i => |v i|) with hσ
  have hmono : Monotone (fun i => |v (σ i)|) := by
    simpa [Function.comp, hσ] using Tuple.monotone_sort (fun i => |v i|)
  have hinj : Function.Injective (fun i => |v (σ i)|) := by
    intro i j hij
    by_contra hne
    exact hdist (σ i) (σ j) (fun h => hne (σ.injective h)) hij
  have hsm : StrictMono (fun i => |v (σ i)|) := hmono.strictMono_of_injective hinj
  refine ⟨⟨σ, fun i => if v (σ i) < 0 then true else false⟩, ?_⟩
  have hc : ∀ i, ((⟨σ, fun i => if v (σ i) < 0 then true else false⟩ : SignedPerm) • v) i
      = |v (σ i)| := by
    intro i
    rw [smul_def]
    show (if (if v (σ i) < 0 then true else false) then -(v (σ i)) else v (σ i)) = |v (σ i)|
    by_cases hlt : v (σ i) < 0
    · simp [hlt, abs_of_neg hlt]
    · simp [hlt, abs_of_nonneg (not_lt.mp hlt)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc 0]; exact abs_pos.mpr (hnz (σ 0))
  · rw [hc 0, hc 1]; exact hsm (by decide : (0 : Fin 3) < 1)
  · rw [hc 1, hc 2]; exact hsm (by decide : (1 : Fin 3) < 2)

theorem cone_ae_covers :
    ∀ᵐ v ∂(volume : Measure V), ∃ g : SignedPerm, g • v ∈ cone := by
  rw [ae_iff]
  refine measure_mono_null ?_ badSet_null
  intro v hv
  by_contra hbad
  exact hv (exists_mem_cone_of_not_bad hbad)

/-! ### The fundamental domain -/

theorem cone_isFundamentalDomain :
    IsFundamentalDomain SignedPerm cone (volume : Measure V) := by
  refine IsFundamentalDomain.mk cone_nullMeasurable cone_ae_covers ?_
  intro g h hgh
  exact (cone_disjoint hgh).aedisjoint

end IndisputableMonolith.Masses.L1bChamberFundamentalDomain
