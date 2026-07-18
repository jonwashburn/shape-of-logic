import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Linking vanishes in low dimension (D = 0, 1)

Mathlib-only leaf module. It restates (verbatim) the content-typed linking
object `linkingComplementH1` and detector `DetectsNontrivialLinking` from
`IndisputableMonolith.Foundation.PublicSpine`, and proves that the detector
fails in dimensions `0` and `1`:

* `not_detects_zero`: the `0`-sphere is a finite (two-point) space, hence
  totally disconnected, hence so is every subspace; singular homology in
  degree `1` of a totally disconnected space vanishes
  (`AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`).
* `not_detects_one`: a continuous injection `S¹ → S¹` is surjective (if it
  missed a point, stereographic projection would give a continuous injection
  `S¹ → ℝ`, impossible since removing the preimage of a middle value keeps
  `S¹` connected while disconnecting the image interval); the complement of
  an embedded circle in `S¹` is therefore empty, and homology of the empty
  space vanishes in degree `1`.

The two definitions are restated with the same implicit arguments and
universes as the parent module, so the parent can glue by `exact`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LinkingVanishingLowDim

/-- Verbatim restatement of `PublicSpine.linkingComplementH1`. -/
noncomputable def linkingComplementH1 (D : ℕ)
    (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)) : ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of {x : TopCat.sphere.{0} D // x ∉ Set.range f})

/-- Verbatim restatement of `PublicSpine.DetectsNontrivialLinking`. -/
def DetectsNontrivialLinking (D : ℕ) : Prop :=
  ∃ f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D),
    Topology.IsEmbedding f ∧
      ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)

/-! ## Dimension 0: the 0-sphere is a two-point space -/

/-- The unit sphere in `ℝ¹` is contained in the two-point set `{e, -e}`. -/
lemma sphere_fin_one_finite :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1).Finite := by
  have hsub : Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 ⊆
      {EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
        EuclideanSpace.single (0 : Fin 1) (-1 : ℝ)} := by
    intro x hx
    rw [EuclideanSpace.sphere_zero_eq _ zero_le_one, Set.mem_setOf_eq,
      Fin.sum_univ_one] at hx
    have h0 : (x 0 - 1) * (x 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h0 with h | h
    · left
      ext i
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [EuclideanSpace.single_apply, if_pos rfl]
      linarith
    · right
      ext i
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [EuclideanSpace.single_apply, if_pos rfl]
      linarith
  exact ((Set.finite_singleton _).insert _).subset hsub

instance : Finite ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
  sphere_fin_one_finite.to_subtype

/-- No embedded circle in the 0-sphere has homologically nontrivial
complement: every subspace of the two-point space `S⁰` is totally
disconnected, so its first singular homology vanishes. -/
theorem not_detects_zero : ¬ DetectsNontrivialLinking 0 := by
  rintro ⟨f, -, hH⟩
  apply hH
  haveI hTD : TotallyDisconnectedSpace ↥(TopCat.sphere.{0} 0) := by
    show TotallyDisconnectedSpace
      (ULift.{0} ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1))
    infer_instance
  haveI : TotallyDisconnectedSpace
      ↥(TopCat.of {x : TopCat.sphere.{0} 0 // x ∉ Set.range f}) :=
    (inferInstance :
      TotallyDisconnectedSpace {x : TopCat.sphere.{0} 0 // x ∉ Set.range f})
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ)
    (TopCat.of {x : TopCat.sphere.{0} 0 // x ∉ Set.range f}) one_ne_zero

/-! ## Dimension 1: an embedded circle fills the whole 1-sphere -/

/-- There is no continuous injection from the metric circle into `ℝ`:
removing the preimage of a strictly-middle value leaves the circle connected
(stereographic projection identifies it with `ℝ¹`), while the image must be
an order-connected set that omits a middle point between two attained
values. -/
theorem no_continuous_injective_circle_to_real
    (g : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → ℝ)
    (hgc : Continuous g) (hginj : Function.Injective g) : False := by
  -- three distinct points on the circle
  have mem1 : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single]; norm_num
  have mem2 : EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single]; norm_num
  have mem3 : EuclideanSpace.single (0 : Fin 2) (-1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single]; norm_num
  set a : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := ⟨_, mem1⟩ with ha
  set b : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := ⟨_, mem2⟩ with hb
  set c : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := ⟨_, mem3⟩ with hc
  have hab : a ≠ b := by
    intro h
    have h0 := congrArg (fun v : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) =>
      (v : EuclideanSpace ℝ (Fin 2)) 0) h
    simp only [ha, hb, EuclideanSpace.single_apply] at h0
    norm_num at h0
  have hac : a ≠ c := by
    intro h
    have h0 := congrArg (fun v : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) =>
      (v : EuclideanSpace ℝ (Fin 2)) 0) h
    simp only [ha, hc, EuclideanSpace.single_apply] at h0
    norm_num at h0
  have hbc : b ≠ c := by
    intro h
    have h0 := congrArg (fun v : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) =>
      (v : EuclideanSpace ℝ (Fin 2)) 0) h
    simp only [hb, hc, EuclideanSpace.single_apply] at h0
    norm_num at h0
  -- among the three (distinct) values pick the strictly-middle one
  have hgab : g a ≠ g b := fun h => hab (hginj h)
  have hgac : g a ≠ g c := fun h => hac (hginj h)
  have hgbc : g b ≠ g c := fun h => hbc (hginj h)
  obtain ⟨x0, y1, y2, hy1, hy2, hlt1, hlt2⟩ :
      ∃ x0 y1 y2 : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1),
        y1 ≠ x0 ∧ y2 ≠ x0 ∧ g y1 < g x0 ∧ g x0 < g y2 := by
    rcases hgab.lt_or_gt with h1 | h1
    · rcases hgbc.lt_or_gt with h2 | h2
      · exact ⟨b, a, c, hab, hbc.symm, h1, h2⟩
      · rcases hgac.lt_or_gt with h3 | h3
        · exact ⟨c, a, b, hac, hbc, h3, h2⟩
        · exact ⟨a, c, b, hac.symm, hab.symm, h3, h1⟩
    · rcases hgac.lt_or_gt with h3 | h3
      · exact ⟨a, b, c, hab.symm, hac.symm, h1, h3⟩
      · rcases hgbc.lt_or_gt with h2 | h2
        · exact ⟨c, b, a, hbc, hac, h2, h3⟩
        · exact ⟨b, c, a, hbc.symm, hab, h2, h1⟩
  -- the circle minus the middle point is connected (stereographic projection)
  haveI fact2 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
    ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  have hconn :
      IsConnected ({x0}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    haveI hct : ConnectedSpace ((stereographic' (1 : ℕ) x0).target) := by
      rw [stereographic'_target]
      exact (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 1))).symm.surjective.connectedSpace
        (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin 1))).symm.continuous
    haveI hcs : ConnectedSpace ((stereographic' (1 : ℕ) x0).source) :=
      (stereographic' (1 : ℕ) x0).toHomeomorphSourceTarget.symm.surjective.connectedSpace
        (stereographic' (1 : ℕ) x0).toHomeomorphSourceTarget.symm.continuous
    rw [← stereographic'_source (n := 1) x0]
    exact isConnected_iff_connectedSpace.mpr hcs
  -- its image omits the middle value, contradicting order-connectedness
  have hy1m : y1 ∈ ({x0}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    Set.mem_compl_singleton_iff.mpr hy1
  have hy2m : y2 ∈ ({x0}ᶜ : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    Set.mem_compl_singleton_iff.mpr hy2
  have himg : IsPreconnected (g '' ({x0}ᶜ)) :=
    hconn.isPreconnected.image g hgc.continuousOn
  have hmid : g x0 ∈ g '' ({x0}ᶜ) :=
    himg.Icc_subset ⟨y1, hy1m, rfl⟩ ⟨y2, hy2m, rfl⟩ ⟨hlt1.le, hlt2.le⟩
  obtain ⟨z, hz, hzeq⟩ := hmid
  exact Set.mem_compl_singleton_iff.mp hz (hginj hzeq)

/-- A continuous injection of the metric circle into itself is surjective:
if it missed a point, composing with the stereographic projection from that
point would give a continuous injection of the circle into `ℝ¹`. -/
theorem continuous_injective_circle_self_surjective
    (f₀ : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) →
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))
    (hc : Continuous f₀) (hinj : Function.Injective f₀) :
    Function.Surjective f₀ := by
  intro p
  by_contra hp
  push_neg at hp
  haveI fact2 : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) :=
    ⟨by norm_num [finrank_euclideanSpace_fin]⟩
  set φ := stereographic' (1 : ℕ) p with hφ
  have hmem : ∀ x, f₀ x ∈ φ.source := by
    intro x
    rw [hφ, stereographic'_source]
    exact Set.mem_compl_singleton_iff.mpr (hp x)
  have hφc : Continuous fun x => φ (f₀ x) :=
    φ.continuousOn.comp_continuous hc hmem
  set g : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) → ℝ :=
    fun x => (φ (f₀ x)) 0 with hg
  have hgc : Continuous g :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp hφc
  have hginj : Function.Injective g := by
    intro x y hxy
    apply hinj
    apply φ.injOn (hmem x) (hmem y)
    ext i
    obtain rfl : i = (0 : Fin 1) := Subsingleton.elim _ _
    exact hxy
  exact (no_continuous_injective_circle_to_real g hgc hginj).elim

/-- No embedded circle in the 1-sphere has homologically nontrivial
complement: the embedding is surjective, so the complement is empty, and
singular homology of the empty space vanishes in degree `1`. -/
theorem not_detects_one : ¬ DetectsNontrivialLinking 1 := by
  rintro ⟨f, hemb, hH⟩
  apply hH
  -- the underlying self-map of the metric circle
  set f₀ : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) →
      ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    fun x =>
      (show ULift.{0} ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) from
        f (show ↥(TopCat.sphere.{0} 1) from ULift.up x)).down with hf₀
  have hc : Continuous f₀ := by
    exact continuous_uliftDown.comp (f.continuous.comp continuous_uliftUp)
  have hinj : Function.Injective f₀ := by
    intro x y h
    have h2 : f (ULift.up x) = f (ULift.up y) := ULift.down_injective h
    have h3 := hemb.injective h2
    exact congrArg ULift.down h3
  have hsurj := continuous_injective_circle_self_surjective f₀ hc hinj
  haveI hE : IsEmpty {x : TopCat.sphere.{0} 1 // x ∉ Set.range f} := by
    constructor
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hsurj
      (show ULift.{0} ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) from x).down
    exact hx ⟨ULift.up y, ULift.down_injective hy⟩
  haveI hTD : TotallyDisconnectedSpace {x : TopCat.sphere.{0} 1 // x ∉ Set.range f} := by
    constructor
    intro t _ _ x hx
    exact (hE.false x).elim
  haveI : TotallyDisconnectedSpace
      ↥(TopCat.of {x : TopCat.sphere.{0} 1 // x ∉ Set.range f}) := hTD
  exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) 1 (ModuleCat.of ℤ ℤ)
    (TopCat.of {x : TopCat.sphere.{0} 1 // x ∉ Set.range f}) one_ne_zero

end LinkingVanishingLowDim
end Foundation
end IndisputableMonolith
