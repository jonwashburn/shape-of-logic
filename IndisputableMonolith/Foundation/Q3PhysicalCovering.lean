import Mathlib
import IndisputableMonolith.Patterns
import IndisputableMonolith.Patterns.GrayCycle

/-!
# Q3 configuration versus Z^3 physical space

Assumed required, then scored:

  A derived map from Q3 configuration space onto Z^3 physical space
  that places the eight-tick cycle at physical voxels.

What the library already names:

* Q3 is `Pattern 3 = Fin 3 → Bool`. The eight ticks live here
  (`grayCycle3Path`, period 8, one-bit steps).
* Physical voxels are `Fin 3 → ℤ` (the D=3 lattice already used as
  `SpaceThetaBridge.VoxelIndex` and as `Gap5RecognitionCarrier.RecSpaceAxis`).
* `Gap5RecognitionCarrier.patternToCell` is the 0-1 chart of one unit cell.
  This module re-derives that chart from the covering, without the gravity
  import cone, and scores the placement claim.

Decoys scored before any implication:

* a map Q3 → Z^3 can hit every voxel
* the eight-tick walk leaves the unit cell
* the Gray clock is the isotropic spatial generator
* a Boolean site coordinate is a bijection with the lattice

Honesty:

* THEOREM: the forced map is the covering `cellParity : Z^3 → Q3`.
  Every voxel carries a Q3 phase. The 0-1 chart `patternToCell` is a
  section, and it is the unique isometric section that sends the empty
  pattern to the origin and the three axis patterns to the three
  positive units.
* THEOREM: there is no surjection Q3 → Z^3 and no injection Z^3 → Q3.
  Ticks cannot occupy all voxels by a map of configurations.
* THEOREM: the Gray walk, charted into Z^3, is an 8-periodic closed
  walk on the unit cell. Ledger time on the product carrier
  `ℕ × Z^3` advances the tick and leaves the voxel fixed.
* THEOREM: the cube has 24 directed one-bit edges; the Gray clock uses
  at most 8 of them. The tick cycle is not the six-neighbor spatial
  generator (the same separator as `PairKernelDeltaSpatialBridgeS5`).
* REFUTED: a map Q3 → Z^3 that places ticks at all physical voxels.
* CONSTRAINT: a worldline that visits many cells is a lift through the
  covering, not a function of Q3 alone. Spatial steps are a second
  generator (minimum-J axis translations), already frame-independent
  in S5.
* WITNESS: `patternToCell ∘ grayCycle3Path` lands in `{0,1}^3` at every
  phase.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace Q3PhysicalCovering

open Patterns

/-! ## Named types -/

/-- Q3 configuration space: three Boolean accounts, eight vertices. -/
abbrev Q3 := Pattern 3

/-- Physical voxel lattice. Definitionally `Fin 3 → ℤ`. -/
abbrev VoxelSpace := Fin 3 → ℤ

/-- Product carrier: ledger time times physical place. A tick is the
    first factor; a voxel is the second. -/
abbrev PhysicalCarrier := ℕ × VoxelSpace

structure ReasonStatus where
  id : String
  title : String
  /-- `"THEOREM"`, `"OPEN"`, `"MODEL"`, or `"REFUTED"`. -/
  status : String

def reasonTable : List ReasonStatus :=
  [ ⟨"C01", "Q3 is Pattern 3 and has eight vertices", "THEOREM"⟩
  , ⟨"C02", "physical voxels are Fin 3 → ℤ", "THEOREM"⟩
  , ⟨"C03", "cellParity : Z^3 → Q3 is a surjective covering", "THEOREM"⟩
  , ⟨"C04", "patternToCell is a section of cellParity", "THEOREM"⟩
  , ⟨"C05", "no surjection Q3 → Z^3 and no injection Z^3 → Q3", "THEOREM"⟩
  , ⟨"C06", "unique isometric section with empty origin and positive axes", "THEOREM"⟩
  , ⟨"C07", "Gray ticks charted into Z^3 stay on the unit cell", "THEOREM"⟩
  , ⟨"C08", "ledger tick on the product carrier leaves the voxel fixed", "THEOREM"⟩
  , ⟨"C09", "Gray clock uses at most 8 of 24 directed cube edges", "THEOREM"⟩
  , ⟨"C10", "a Q3→Z^3 map places ticks at all physical voxels", "REFUTED"⟩
  ]

/-! ## C01–C02. The two spaces -/

theorem C01_q3_card : Fintype.card Q3 = 8 := by
  simpa using Patterns.card_pattern 3

theorem C02_voxelSpace_def : VoxelSpace = (Fin 3 → ℤ) :=
  rfl

theorem voxelSpace_infinite : Infinite VoxelSpace :=
  Infinite.of_injective (fun n : ℤ => fun i : Fin 3 => if i = 0 then n else 0)
    (fun a b h => by
      have := congrFun h 0
      simpa using this)

/-! ## The covering and the 0-1 section -/

/-- Boolean bit as a 0-1 integer. -/
def bitZ (b : Bool) : ℤ := if b then 1 else 0

/-- Unit-cell chart: each Q3 vertex as a corner of `{0,1}^3`.
    This is the same function as `Gap5RecognitionCarrier.patternToCell`. -/
def patternToCell (p : Q3) : VoxelSpace :=
  fun i => bitZ (p i)

/-- Covering map: each voxel carries the Q3 phase of its coordinate parities. -/
def cellParity (x : VoxelSpace) : Q3 :=
  fun i => decide (x i % 2 = 1)

/- `Pattern` is a `def`, not an `abbrev`, so instance search does not see
   through it; equality on `Q3` must be registered by hand. -/
instance : DecidableEq Q3 := by
  unfold Q3 Pattern
  infer_instance

instance : DecidableRel (fun p q : Q3 => OneBitDiff p q) := by
  intro p q
  unfold OneBitDiff ExistsUnique
  infer_instance

/-- Manhattan distance on the physical lattice. -/
def manhattan (x y : VoxelSpace) : ℕ :=
  (x 0 - y 0).natAbs + (x 1 - y 1).natAbs + (x 2 - y 2).natAbs

def zeroPat : Q3 := fun _ => false

def axisPat (i : Fin 3) : Q3 :=
  fun j => decide (j = i)

def twoPat (i j : Fin 3) : Q3 :=
  fun k => decide (k = i ∨ k = j)

def fullPat : Q3 := fun _ => true

def axisUnit (i : Fin 3) : VoxelSpace :=
  fun j => if j = i then 1 else 0

theorem C04_cellParity_patternToCell (p : Q3) :
    cellParity (patternToCell p) = p := by
  funext i
  cases hp : p i <;> simp [cellParity, patternToCell, bitZ, hp]

theorem C03_cellParity_surjective : Function.Surjective cellParity :=
  fun p => ⟨patternToCell p, C04_cellParity_patternToCell p⟩

theorem patternToCell_injective : Function.Injective patternToCell := by
  intro p q h
  funext i
  have hi := congrFun h i
  simp only [patternToCell, bitZ] at hi
  cases hp : p i <;> cases hq : q i <;> simp [hp, hq] at hi ⊢

theorem patternToCell_zero : patternToCell zeroPat = fun _ => 0 := by
  funext i
  simp [patternToCell, bitZ, zeroPat]

theorem patternToCell_axis (i : Fin 3) :
    patternToCell (axisPat i) = axisUnit i := by
  funext j
  by_cases h : j = i <;> simp [patternToCell, bitZ, axisPat, axisUnit, h]

/-! ## C05. No placement of all voxels by a Q3 map -/

theorem C05_no_surjection_Q3_to_voxels (f : Q3 → VoxelSpace) :
    ¬ Function.Surjective f := by
  haveI : Infinite VoxelSpace := voxelSpace_infinite
  exact not_surjective_finite_infinite f

theorem C05_no_injection_voxels_to_Q3 (f : VoxelSpace → Q3) :
    ¬ Function.Injective f := by
  haveI : Infinite VoxelSpace := voxelSpace_infinite
  exact not_injective_infinite_finite f

/-! ## C08. Ticks on the product carrier do not move the voxel -/

def tickOnly (s : PhysicalCarrier) : PhysicalCarrier :=
  (s.1 + 1, s.2)

theorem C08_tickOnly_preserves_voxel (s : PhysicalCarrier) :
    (tickOnly s).2 = s.2 :=
  rfl

theorem C08_tickOnly_advances_time (s : PhysicalCarrier) :
    (tickOnly s).1 = s.1 + 1 :=
  rfl

/-! ## C07. Charted Gray ticks stay on the unit cell -/

def chartedTick (t : Fin 8) : VoxelSpace :=
  patternToCell (grayCycle3Path t)

theorem chartedTick_in_unit_cell (t : Fin 8) (i : Fin 3) :
    chartedTick t i = 0 ∨ chartedTick t i = 1 := by
  simp only [chartedTick, patternToCell, bitZ]
  cases grayCycle3Path t i <;> simp

theorem C07_charted_gray_image_finite :
    (Set.range chartedTick).Finite :=
  Set.finite_range chartedTick

theorem C07_charted_gray_card_le_eight :
    Fintype.card (Set.range chartedTick) ≤ 8 := by
  classical
  simpa using Fintype.card_range_le chartedTick

theorem C07_charted_gray_not_all_voxels :
    ¬ Set.range chartedTick = Set.univ := by
  intro h
  have hfin : (Set.univ : Set VoxelSpace).Finite := by
    rw [← h]
    exact C07_charted_gray_image_finite
  haveI : Infinite VoxelSpace := voxelSpace_infinite
  exact Set.infinite_univ hfin

/-! ## C06. The 0-1 chart is the unique positive isometric section -/

lemma section_mod
    (s : Q3 → VoxelSpace)
    (hsec : ∀ p, cellParity (s p) = p)
    (p : Q3) (i : Fin 3) :
    s p i % 2 = bitZ (p i) := by
  have h := congrFun (hsec p) i
  simp only [cellParity] at h
  cases hp : p i
  · have : s p i % 2 ≠ 1 := by
      intro h1
      simp [hp, h1] at h
    have h01 : s p i % 2 = 0 ∨ s p i % 2 = 1 := Int.emod_two_eq_zero_or_one _
    simp [bitZ, hp, h01.resolve_right this]
  · have : s p i % 2 = 1 := by
      simpa [hp, decide_eq_true_eq] using h
    simp [bitZ, hp, this]

lemma section_decomp
    (s : Q3 → VoxelSpace)
    (hsec : ∀ p, cellParity (s p) = p)
    (p : Q3) (i : Fin 3) :
    s p i = 2 * (s p i / 2) + bitZ (p i) := by
  have hmod := section_mod s hsec p i
  omega

lemma oneBitDiff_unique_axis {p q : Q3} (h : OneBitDiff p q) :
    ∃ k : Fin 3, p k ≠ q k ∧ ∀ j : Fin 3, j ≠ k → p j = q j := by
  rcases h with ⟨k, hk, huniq⟩
  refine ⟨k, hk, ?_⟩
  intro j hj
  by_contra hne
  exact hj (huniq j hne)

lemma manhattan_eq_one_iff (x y : VoxelSpace) :
    manhattan x y = 1 ↔
      ∃ k : Fin 3, (x k - y k).natAbs = 1 ∧ ∀ j : Fin 3, j ≠ k → x j = y j := by
  constructor
  · intro h
    have hsum : (x 0 - y 0).natAbs + (x 1 - y 1).natAbs + (x 2 - y 2).natAbs = 1 := h
    rcases Nat.eq_zero_or_pos (x 0 - y 0).natAbs with h0 | h0
    · rcases Nat.eq_zero_or_pos (x 1 - y 1).natAbs with h1 | h1
      · have h2 : (x 2 - y 2).natAbs = 1 := by omega
        refine ⟨2, h2, ?_⟩
        intro j hj
        fin_cases j
        · show x 0 = y 0
          have := Int.natAbs_eq_zero.mp h0; omega
        · show x 1 = y 1
          have := Int.natAbs_eq_zero.mp h1; omega
        · exact absurd rfl hj
      · have : (x 1 - y 1).natAbs = 1 := by omega
        have h2 : (x 2 - y 2).natAbs = 0 := by omega
        refine ⟨1, this, ?_⟩
        intro j hj
        fin_cases j
        · show x 0 = y 0
          have := Int.natAbs_eq_zero.mp h0; omega
        · exact absurd rfl hj
        · show x 2 = y 2
          have := Int.natAbs_eq_zero.mp h2; omega
    · have : (x 0 - y 0).natAbs = 1 := by omega
      have h1 : (x 1 - y 1).natAbs = 0 := by omega
      have h2 : (x 2 - y 2).natAbs = 0 := by omega
      refine ⟨0, this, ?_⟩
      intro j hj
      fin_cases j
      · exact absurd rfl hj
      · show x 1 = y 1
        have := Int.natAbs_eq_zero.mp h1; omega
      · show x 2 = y 2
        have := Int.natAbs_eq_zero.mp h2; omega
  · rintro ⟨k, hk, hrest⟩
    fin_cases k
    · have h1 : x 1 = y 1 := hrest 1 (by decide)
      have h2 : x 2 = y 2 := hrest 2 (by decide)
      have hk' : (x 0 - y 0).natAbs = 1 := hk
      simp [manhattan, hk', h1, h2]
    · have h0 : x 0 = y 0 := hrest 0 (by decide)
      have h2 : x 2 = y 2 := hrest 2 (by decide)
      have hk' : (x 1 - y 1).natAbs = 1 := hk
      simp [manhattan, hk', h0, h2]
    · have h0 : x 0 = y 0 := hrest 0 (by decide)
      have h1 : x 1 = y 1 := hrest 1 (by decide)
      have hk' : (x 2 - y 2).natAbs = 1 := hk
      simp [manhattan, hk', h0, h1]

lemma opposite_parity_of_natAbs_one {a b : ℤ} (h : (a - b).natAbs = 1) :
    a % 2 ≠ b % 2 := by
  have := Int.natAbs_eq_iff.mp h
  omega

lemma isometric_changes_flipped_axis
    (s : Q3 → VoxelSpace)
    (hsec : ∀ p, cellParity (s p) = p)
    (hadj : ∀ p q, OneBitDiff p q → manhattan (s p) (s q) = 1)
    {p q : Q3} (h : OneBitDiff p q) :
    ∃ k : Fin 3, p k ≠ q k ∧
      (s p k - s q k).natAbs = 1 ∧
      ∀ j : Fin 3, j ≠ k → s p j = s q j := by
  obtain ⟨k, hk, hbits⟩ := oneBitDiff_unique_axis h
  obtain ⟨k', hk', hrest⟩ := (manhattan_eq_one_iff (s p) (s q)).mp (hadj p q h)
  have : k' = k := by
    by_contra hne
    have hsame : p k' = q k' := hbits k' hne
    have hpar : s p k' % 2 = s q k' % 2 := by
      rw [section_mod s hsec p k', section_mod s hsec q k', hsame]
    exact opposite_parity_of_natAbs_one hk' hpar
  subst this
  exact ⟨k', hk, hk', hrest⟩

lemma even_plus_odd_natAbs {n : ℤ} {b : Bool} :
    (2 * n + bitZ b).natAbs = 1 → n = 0 ∨ (n = -1 ∧ b = true) := by
  intro h
  cases b
  · -- 2n, |2n|=1 is impossible
    simp [bitZ] at h
    have : (2 * n).natAbs = 2 * n.natAbs := by
      simp [Int.natAbs_mul]
    rw [this] at h
    omega
  · simp [bitZ] at h
    have hn : n = 0 ∨ n = -1 := by
      have : 2 * n + 1 = 1 ∨ 2 * n + 1 = -1 := by
        have := Int.natAbs_eq_iff.mp h
        omega
      omega
    rcases hn with rfl | rfl <;> simp

lemma axisPat_oneBit (i : Fin 3) : OneBitDiff zeroPat (axisPat i) := by
  refine ⟨i, ?_, ?_⟩
  · simp [zeroPat, axisPat]
  · intro k hk
    by_contra hne
    simp [zeroPat, axisPat, hne] at hk

lemma twoPat_oneBit_left {i j : Fin 3} (hne : i ≠ j) :
    OneBitDiff (axisPat i) (twoPat i j) := by
  refine ⟨j, ?_, ?_⟩
  · have hji : ¬ (j = i) := fun hji => hne hji.symm
    simp [axisPat, twoPat, hji]
  · intro k hk
    by_contra hne'
    simp [axisPat, twoPat, hne'] at hk

lemma twoPat_oneBit_right {i j : Fin 3} (hne : i ≠ j) :
    OneBitDiff (axisPat j) (twoPat i j) := by
  refine ⟨i, ?_, ?_⟩
  · have hij : ¬ (i = j) := hne
    simp [axisPat, twoPat, hij]
  · intro k hk
    by_contra hne'
    simp [axisPat, twoPat, hne'] at hk

lemma fullPat_oneBit_from_two01 : OneBitDiff (twoPat 0 1) fullPat := by
  refine ⟨2, ?_, ?_⟩
  · simp [twoPat, fullPat]
  · intro k hk
    fin_cases k <;> simp_all [twoPat, fullPat]

lemma fullPat_oneBit_from_two02 : OneBitDiff (twoPat 0 2) fullPat := by
  refine ⟨1, ?_, ?_⟩
  · simp [twoPat, fullPat]
  · intro k hk
    fin_cases k <;> simp_all [twoPat, fullPat]

lemma toNat3_lt (p : Q3) : toNat3 p < 8 := by
  revert p
  decide

lemma pattern3_toNat3 (p : Q3) :
    pattern3 ⟨toNat3 p, toNat3_lt p⟩ = p := by
  revert p
  decide

theorem patternToCell_is_isometric_section :
    (∀ p, cellParity (patternToCell p) = p) ∧
      patternToCell zeroPat = (fun _ => 0) ∧
      (∀ i, patternToCell (axisPat i) = axisUnit i) ∧
      (∀ p q, OneBitDiff p q → manhattan (patternToCell p) (patternToCell q) = 1) := by
  refine ⟨C04_cellParity_patternToCell, patternToCell_zero, patternToCell_axis, ?_⟩
  intro p q h
  revert p q h
  decide

/-- **C06.** An isometric section of `cellParity` that sends the empty
    pattern to the origin and the three axis patterns to the three
    positive units is the 0-1 chart. -/
theorem C06_unique_positive_isometric_section
    (s : Q3 → VoxelSpace)
    (h0 : s zeroPat = fun _ => 0)
    (haxis : ∀ i, s (axisPat i) = axisUnit i)
    (hsec : ∀ p, cellParity (s p) = p)
    (hadj : ∀ p q, OneBitDiff p q → manhattan (s p) (s q) = 1) :
    s = patternToCell := by
  have htwo : ∀ {i j : Fin 3} (hne : i ≠ j), s (twoPat i j) = patternToCell (twoPat i j) := by
    intro i j hne
    obtain ⟨kL, hkLbit, hkLchg, hkLrest⟩ :=
      isometric_changes_flipped_axis s hsec hadj (twoPat_oneBit_left hne)
    obtain ⟨kR, hkRbit, hkRchg, hkRrest⟩ :=
      isometric_changes_flipped_axis s hsec hadj (twoPat_oneBit_right hne)
    have hkLj : kL = j := by
      by_contra hkLj
      apply hkLbit
      simp [axisPat, twoPat, hkLj]
    have hkRi : kR = i := by
      by_contra hkRi
      apply hkRbit
      simp [axisPat, twoPat, hkRi]
    have hLrest : ∀ k, k ≠ j → s (axisPat i) k = s (twoPat i j) k :=
      hkLj ▸ hkLrest
    have hRrest : ∀ k, k ≠ i → s (axisPat j) k = s (twoPat i j) k :=
      hkRi ▸ hkRrest
    funext k
    rw [haxis i] at hLrest
    rw [haxis j] at hRrest
    by_cases hki : k = i
    · have hkj : k ≠ j := by rw [hki]; exact hne
      have hfix := (hLrest k hkj).symm
      rw [hfix]
      simp [axisUnit, patternToCell, twoPat, bitZ, hki, hkj]
    · by_cases hkj : k = j
      · have hfix := (hRrest k hki).symm
        rw [hfix]
        simp [axisUnit, patternToCell, twoPat, bitZ, hki, hkj]
      · have hfix := (hLrest k hkj).symm
        rw [hfix]
        simp [axisUnit, patternToCell, twoPat, bitZ, hki, hkj]
  have hfull : s fullPat = patternToCell fullPat := by
    obtain ⟨k, hkbit, _, hkrest⟩ :=
      isometric_changes_flipped_axis s hsec hadj fullPat_oneBit_from_two01
    have hk2 : k = 2 := by
      by_contra hk2
      apply hkbit
      fin_cases k <;> simp_all [twoPat, fullPat]
    subst hk2
    obtain ⟨k', hk'bit, _, hk'rest⟩ :=
      isometric_changes_flipped_axis s hsec hadj fullPat_oneBit_from_two02
    have hk1 : k' = 1 := by
      by_contra hk1
      apply hk'bit
      fin_cases k' <;> simp_all [twoPat, fullPat]
    subst hk1
    have h01 := htwo (by decide : (0 : Fin 3) ≠ 1)
    have h02 := htwo (by decide : (0 : Fin 3) ≠ 2)
    funext k
    fin_cases k
    · have : s (twoPat 0 1) 0 = s fullPat 0 := hkrest 0 (by decide)
      rw [h01] at this
      simp [this.symm, patternToCell, twoPat, fullPat, bitZ]
    · have hfix1 : s (twoPat 0 1) 1 = s fullPat 1 := hkrest 1 (by decide)
      rw [h01] at hfix1
      simp [hfix1.symm, patternToCell, twoPat, fullPat, bitZ]
    · have hfix2 : s (twoPat 0 2) 2 = s fullPat 2 := hk'rest 2 (by decide)
      rw [h02] at hfix2
      simp [hfix2.symm, patternToCell, twoPat, fullPat, bitZ]
  funext p
  have hcases : p = zeroPat ∨ p = axisPat 0 ∨ p = axisPat 1 ∨ p = axisPat 2 ∨
      p = twoPat 0 1 ∨ p = twoPat 0 2 ∨ p = twoPat 1 2 ∨ p = fullPat := by
    revert p
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0.trans patternToCell_zero.symm
  · exact (haxis 0).trans (patternToCell_axis 0).symm
  · exact (haxis 1).trans (patternToCell_axis 1).symm
  · exact (haxis 2).trans (patternToCell_axis 2).symm
  · exact htwo (by decide : (0 : Fin 3) ≠ 1)
  · exact htwo (by decide : (0 : Fin 3) ≠ 2)
  · exact htwo (by decide : (1 : Fin 3) ≠ 2)
  · exact hfull

/-! ## C09. The Gray clock is not the cube's spatial generator -/

def DirectedCubeEdge : Type :=
  { pq : Q3 × Q3 // OneBitDiff pq.1 pq.2 }

instance : DecidableEq DirectedCubeEdge := by
  unfold DirectedCubeEdge
  infer_instance

instance : Fintype DirectedCubeEdge :=
  Subtype.fintype _

theorem C09_directed_cube_edge_card :
    Fintype.card DirectedCubeEdge = 24 := by
  decide

def grayDirectedEdge (t : Fin 8) : DirectedCubeEdge :=
  ⟨(grayCycle3Path t, grayCycle3Path (t + 1)), grayCycle3_oneBit_step t⟩

theorem C09_gray_uses_at_most_eight_directed_edges :
    Fintype.card (Set.range grayDirectedEdge) ≤ 8 := by
  classical
  simpa using Fintype.card_range_le grayDirectedEdge

theorem C09_gray_misses_directed_edges :
    Fintype.card (Set.range grayDirectedEdge) < Fintype.card DirectedCubeEdge := by
  have hle : Fintype.card (Set.range grayDirectedEdge) ≤ 8 :=
    C09_gray_uses_at_most_eight_directed_edges
  have hcard : Fintype.card DirectedCubeEdge = 24 :=
    C09_directed_cube_edge_card
  omega

/-! ## C10. The placement claim is refuted -/

/-- A placement of ticks at physical voxels by a map of Q3 configurations
    would have to be a surjection Q3 → Z^3, or at least hit every voxel
    along the Gray walk. Both fail. -/
theorem C10_no_Q3_map_occupies_all_voxels :
    (∀ f : Q3 → VoxelSpace, ¬ Function.Surjective f) ∧
      ¬ Set.range chartedTick = Set.univ :=
  ⟨C05_no_surjection_Q3_to_voxels, C07_charted_gray_not_all_voxels⟩

/-- The forced object: every physical voxel carries a Q3 phase, the 0-1
    chart is a section, ticks stay on that cell, and ledger time does not
    move the voxel. -/
theorem q3_physical_covering_forced :
    Function.Surjective cellParity ∧
      (∀ p, cellParity (patternToCell p) = p) ∧
      Function.Injective patternToCell ∧
      (∀ f : Q3 → VoxelSpace, ¬ Function.Surjective f) ∧
      (∀ s : PhysicalCarrier, (tickOnly s).2 = s.2) ∧
      Fintype.card (Set.range grayDirectedEdge) < Fintype.card DirectedCubeEdge :=
  ⟨C03_cellParity_surjective,
   C04_cellParity_patternToCell,
   patternToCell_injective,
   C05_no_surjection_Q3_to_voxels,
   C08_tickOnly_preserves_voxel,
   C09_gray_misses_directed_edges⟩

def coveringReasonCensus : List ReasonStatus := reasonTable

#print axioms C03_cellParity_surjective
#print axioms C05_no_surjection_Q3_to_voxels
#print axioms C06_unique_positive_isometric_section
#print axioms C08_tickOnly_preserves_voxel
#print axioms C10_no_Q3_map_occupies_all_voxels
#print axioms q3_physical_covering_forced

end Q3PhysicalCovering
end Foundation
end IndisputableMonolith
