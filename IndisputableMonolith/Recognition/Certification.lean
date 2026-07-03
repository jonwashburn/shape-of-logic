import Mathlib

namespace IndisputableMonolith
namespace Recognition
namespace Certification

noncomputable section
open Classical

/-- Closed interval with endpoints `lo ≤ hi`. -/
structure Interval where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi

@[simp] def memI (I : Interval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

@[simp] def width (I : Interval) : ℝ := I.hi - I.lo

/-- If `x,y` lie in the same interval `I`, then `|x − y| ≤ width(I)`. -/
lemma abs_sub_le_width_of_memI {I : Interval} {x y : ℝ}
  (hx : memI I x) (hy : memI I y) : |x - y| ≤ width I := by
  have : I.lo ≤ x ∧ x ≤ I.hi := hx
  have : I.lo ≤ y ∧ y ≤ I.hi := hy
  have : x - y ≤ I.hi - I.lo := by linarith
  have : y - x ≤ I.hi - I.lo := by linarith
  have : -(I.hi - I.lo) ≤ x - y ∧ x - y ≤ I.hi - I.lo := by
    constructor
    · linarith
    · linarith
  simpa [width, abs_le] using this

/-! ## Certificate schema -/

/-- Anchor certificate: per-species residue intervals plus charge-wise gap intervals. -/
structure AnchorCert (Species : Type) where
  M0 : Interval
  Ires : Species → Interval
  center : Int → ℝ
  eps : Int → ℝ
  eps_nonneg : ∀ z, 0 ≤ eps z

@[simp] def Igap {Species : Type} (C : AnchorCert Species) (z : Int) : Interval :=
{ lo := C.center z - C.eps z
, hi := C.center z + C.eps z
, lo_le_hi := by have := C.eps_nonneg z; linarith }

/-- Validity of a certificate w.r.t. a charge map `Z` and display function `Fgap`. -/
structure Valid {Species : Type} (Z : Species → Int) (Fgap : Int → ℝ) (C : AnchorCert Species) : Prop where
  M0_pos : 0 < C.M0.lo
  Fgap_in : ∀ i : Species, memI (Igap C (Z i)) (Fgap (Z i))
  Ires_in_Igap : ∀ i : Species,
    (Igap C (Z i)).lo ≤ (C.Ires i).lo ∧ (C.Ires i).hi ≤ (Igap C (Z i)).hi

lemma M0_pos_of_cert {Species : Type} {Z : Species → Int} {Fgap : Int → ℝ}
    {C : AnchorCert Species} (hC : Valid Z Fgap C) : 0 < C.M0.lo :=
  hC.M0_pos

/-- Certificate replacement for the anchor identity (inequality form). -/
lemma anchorIdentity_cert {Species : Type} {Z : Species → Int} {Fgap : Int → ℝ}
    {C : AnchorCert Species} (hC : Valid Z Fgap C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i)) :
  ∀ i : Species, |res i - Fgap (Z i)| ≤ 2 * C.eps (Z i) := by
  intro i
  have hF : memI (Igap C (Z i)) (Fgap (Z i)) := hC.Fgap_in i
  have hI : (Igap C (Z i)).lo ≤ (C.Ires i).lo ∧ (C.Ires i).hi ≤ (Igap C (Z i)).hi :=
    hC.Ires_in_Igap i
  have hr : memI (Igap C (Z i)) (res i) := by
    have hr0 := hres i
    refine ⟨le_trans hI.1 hr0.1, le_trans hr0.2 hI.2⟩
  have hbound :=
    abs_sub_le_width_of_memI (I := Igap C (Z i)) (x := res i) (y := Fgap (Z i)) hr hF
  -- width(Igap) = 2*eps
  have hw :
      width (Igap C (Z i)) = 2 * C.eps (Z i) := by
    simp [Igap, width]
    ring
  simpa [hw, two_mul] using hbound

/-- Equal‑Z degeneracy (inequality form) from a certificate. -/
lemma equalZ_residue_of_cert {Species : Type} {Z : Species → Int} {Fgap : Int → ℝ}
    {C : AnchorCert Species} (hC : Valid Z Fgap C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i))
  {i j : Species} (hZ : Z i = Z j) :
  |res i - res j| ≤ 2 * C.eps (Z i) := by
  have hI_i : (Igap C (Z i)).lo ≤ (C.Ires i).lo ∧ (C.Ires i).hi ≤ (Igap C (Z i)).hi :=
    hC.Ires_in_Igap i
  have hI_j : (Igap C (Z j)).lo ≤ (C.Ires j).lo ∧ (C.Ires j).hi ≤ (Igap C (Z j)).hi :=
    hC.Ires_in_Igap j
  have hres_i : memI (Igap C (Z i)) (res i) := by
    have hr0 := hres i
    exact ⟨le_trans hI_i.1 hr0.1, le_trans hr0.2 hI_i.2⟩
  have hres_j : memI (Igap C (Z i)) (res j) := by
    have hr0 := hres j
    have hlo_j : (Igap C (Z i)).lo ≤ (C.Ires j).lo := by simpa [hZ] using hI_j.1
    have hhi_j : (C.Ires j).hi ≤ (Igap C (Z i)).hi := by simpa [hZ] using hI_j.2
    exact ⟨le_trans hlo_j hr0.1, le_trans hr0.2 hhi_j⟩
  have hbound :=
    abs_sub_le_width_of_memI (I := Igap C (Z i)) (x := res i) (y := res j) hres_i hres_j
  have hw :
      width (Igap C (Z i)) = 2 * C.eps (Z i) := by
    simp [Igap, width]
    ring
  simpa [hw, two_mul] using hbound

/-! ### Zero-width anchor certificate (exact equality) -/

/-- Zero-width certificate: each interval collapses to the center value `Fgap(Z i)`. -/
noncomputable def zeroWidthCert {Species : Type} (Z : Species → Int) (Fgap : Int → ℝ) : AnchorCert Species :=
{ M0 := { lo := 1, hi := 1, lo_le_hi := by norm_num }
, Ires := fun i => { lo := Fgap (Z i), hi := Fgap (Z i), lo_le_hi := by linarith }
, center := fun z => Fgap z
, eps := fun _ => 0
, eps_nonneg := by intro _; norm_num }

lemma zeroWidthCert_valid {Species : Type} (Z : Species → Int) (Fgap : Int → ℝ) :
    Valid Z Fgap (zeroWidthCert Z Fgap) := by
  refine {
    M0_pos := by simp [zeroWidthCert]
  , Fgap_in := by
      intro i
      dsimp [zeroWidthCert, Igap, memI]
      constructor <;> linarith
  , Ires_in_Igap := by
      intro i
      dsimp [zeroWidthCert, Igap]
      constructor <;> linarith
  }

/-- Exact anchor identity from a zero-width certificate. -/
lemma anchorIdentity_of_zeroWidthCert {Species : Type} (Z : Species → Int) (Fgap : Int → ℝ)
    (res : Species → ℝ) (hres : ∀ i, memI ((zeroWidthCert Z Fgap).Ires i) (res i)) :
  ∀ i : Species, res i = Fgap (Z i) := by
  intro i
  have h := hres i
  dsimp [zeroWidthCert, memI] at h
  exact le_antisymm h.2 h.1

end

end Certification
end Recognition
end IndisputableMonolith
