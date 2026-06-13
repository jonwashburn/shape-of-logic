import Mathlib.Topology.Homotopy.Lifting
import IndisputableMonolith.Foundation.CircleLifting

/-!
# The local winding (displacement) invariant on paths in `TopCat.sphere 1`

This module defines the winding / displacement of a path in the exact
`TopCat.sphere 1` object by lifting it through the covering map
`CircleCovering.isCoveringMap_trigCirclePoint` and measuring how far the lift
travels in `ℝ`.

The central technical result is `pathDisplacement_eq`: the displacement computed
from the canonical (choice-based) lift agrees with the endpoint difference of
*any* continuous lift.  This is what makes the displacement a usable invariant:
it lets every later computation pick whatever explicit lift is convenient.  The
proof is the deck-transformation argument: two lifts of one path that start in
the same fiber differ by a constant element of the deck group `2πℤ`, by the
covering's lift-uniqueness theorem (`IsCoveringMap.eq_of_comp_eq`) and the period
invariance of `trigCirclePoint`.

No axioms, `sorry`, or project-local `S¹` replacements are used.
-/

namespace IndisputableMonolith
namespace Foundation
namespace CircleWinding

open CircleParam CircleCovering CircleLifting
open scoped Real Topology unitInterval

noncomputable section

/-- Abbreviation for the carrier of the exact `TopCat.sphere 1` object. -/
abbrev SphereOne : Type := TopCat.sphere 1

/-- The trigonometric covering is surjective: every point of `TopCat.sphere 1`
is `trigCirclePoint` of some real angle. -/
theorem trigCirclePoint_surjective : Function.Surjective trigCirclePoint := by
  intro y
  rw [← ulift_carrierCovering_eq_trig]
  obtain ⟨c, hc⟩ := (Homeomorph.ulift (X := SphereOneCarrier)).symm.surjective y
  obtain ⟨z, hz⟩ := circleHomeoCarrier.surjective c
  refine ⟨Complex.arg (z : ℂ), ?_⟩
  simp only [Function.comp_apply, carrierCovering]
  rw [Circle.exp_arg, hz, hc]

/-- Period invariance of the covering: shifting the angle by an integer number of
full turns `2π` does not change the point. -/
theorem trigCirclePoint_add_intMul_period (x : ℝ) (k : ℤ) :
    trigCirclePoint (x + (k : ℝ) * (2 * Real.pi)) = trigCirclePoint x := by
  rw [trigCirclePoint_eq_iff]
  exact ⟨k, rfl⟩

/-- A chosen real lift of the initial point of a path. -/
def pathLiftStart (γ : C(I, SphereOne)) : ℝ :=
  (trigCirclePoint_surjective (γ 0)).choose

theorem pathLiftStart_spec (γ : C(I, SphereOne)) :
    trigCirclePoint (pathLiftStart γ) = γ 0 :=
  (trigCirclePoint_surjective (γ 0)).choose_spec

/-- The canonical continuous lift of a path, starting at `pathLiftStart`. -/
def pathLift (γ : C(I, SphereOne)) : C(I, ℝ) :=
  isCoveringMap_trig.liftPath γ (pathLiftStart γ) (pathLiftStart_spec γ).symm

theorem pathLift_lifts (γ : C(I, SphereOne)) :
    trigCirclePoint ∘ (pathLift γ) = γ :=
  isCoveringMap_trig.liftPath_lifts γ (pathLiftStart γ) (pathLiftStart_spec γ).symm

theorem pathLift_zero (γ : C(I, SphereOne)) :
    pathLift γ 0 = pathLiftStart γ :=
  isCoveringMap_trig.liftPath_zero γ (pathLiftStart γ) (pathLiftStart_spec γ).symm

/-- The displacement of a path: how far its canonical lift travels in `ℝ`. -/
def pathDisplacement (γ : C(I, SphereOne)) : ℝ :=
  pathLift γ 1 - pathLift γ 0

/-- **Lift independence.**  The displacement computed from the canonical lift
equals the endpoint difference of *any* continuous lift `Γ` of the path.  Two
lifts that agree on the same fiber differ by a constant in the deck group `2πℤ`,
so their endpoint differences coincide. -/
theorem pathDisplacement_eq (γ : C(I, SphereOne)) (Γ : C(I, ℝ))
    (hΓ : trigCirclePoint ∘ (Γ : I → ℝ) = γ) :
    pathDisplacement γ = Γ 1 - Γ 0 := by
  set Γ' := pathLift γ with hΓ'def
  -- The two lift starts lie in the same fiber, hence differ by `k • (2π)`.
  have hfib : trigCirclePoint (Γ 0) = trigCirclePoint (Γ' 0) := by
    have h1 : trigCirclePoint (Γ 0) = γ 0 := congrFun hΓ 0
    have h2 : trigCirclePoint (Γ' 0) = γ 0 := congrFun (pathLift_lifts γ) 0
    rw [h1, h2]
  obtain ⟨k, hk⟩ := (trigCirclePoint_eq_iff (Γ 0) (Γ' 0)).1 hfib
  set c : ℝ := (k : ℝ) * (2 * Real.pi) with hcdef
  -- `Γ' + c` is also a lift, and agrees with `Γ` at `0`.
  have hshift_lifts : trigCirclePoint ∘ (fun t : I => Γ' t + c) = γ := by
    funext t
    have : trigCirclePoint (Γ' t + c) = trigCirclePoint (Γ' t) :=
      trigCirclePoint_add_intMul_period (Γ' t) k
    rw [Function.comp_apply, this]
    exact congrFun (pathLift_lifts γ) t
  have hagree0 : Γ 0 = (fun t : I => Γ' t + c) 0 := by
    simp only [hcdef]; rw [hk]
  -- Lift uniqueness on the connected interval forces equality.
  have huniq : (fun t : I => Γ t) = (fun t : I => Γ' t + c) :=
    isCoveringMap_trig.eq_of_comp_eq Γ.continuous
      (Γ'.continuous.add continuous_const)
      (by rw [hΓ, hshift_lifts]) 0 hagree0
  have hone : Γ 1 = Γ' 1 + c := congrFun huniq 1
  have hzero : Γ 0 = Γ' 0 + c := congrFun huniq 0
  simp only [pathDisplacement, ← hΓ'def]
  rw [hone, hzero]; ring

/-- The displacement of the canonical lift is exactly its own endpoint
difference (the defining special case of `pathDisplacement_eq`). -/
theorem pathDisplacement_self (γ : C(I, SphereOne)) :
    pathDisplacement γ = pathLift γ 1 - pathLift γ 0 := rfl

/-- The unit-interval reversal `t ↦ 1 - t` as a continuous self-map. -/
def intervalReverse : C(I, I) := ⟨unitInterval.symm, unitInterval.continuous_symm⟩

/-- The reverse of a path in `S¹`, reparameterised by `t ↦ 1 - t`. -/
def reversePath (γ : C(I, SphereOne)) : C(I, SphereOne) := γ.comp intervalReverse

@[simp] theorem reversePath_apply (γ : C(I, SphereOne)) (t : I) :
    reversePath γ t = γ (unitInterval.symm t) := rfl

/-- **Displacement of a reversed path.**  Traversing a path backwards negates its
displacement, because the canonical lift composed with `t ↦ 1 - t` lifts the
reversed path and its endpoint difference flips sign. -/
theorem pathDisplacement_reverse (γ : C(I, SphereOne)) :
    pathDisplacement (reversePath γ) = - pathDisplacement γ := by
  have hlift :
      trigCirclePoint ∘ (((pathLift γ).comp intervalReverse) : I → ℝ) = reversePath γ := by
    funext t
    show trigCirclePoint (pathLift γ (unitInterval.symm t)) = γ (unitInterval.symm t)
    exact congrFun (pathLift_lifts γ) (unitInterval.symm t)
  rw [pathDisplacement_eq (reversePath γ) ((pathLift γ).comp intervalReverse) hlift]
  show pathLift γ (unitInterval.symm 1) - pathLift γ (unitInterval.symm 0) = - pathDisplacement γ
  rw [unitInterval.symm_one, unitInterval.symm_zero]
  rw [pathDisplacement_self]
  ring

/-- Paths homotopic relative to their endpoints share their initial point. -/
theorem homotopicRel_apply_zero {γ δ : C(I, SphereOne)}
    (h : γ.HomotopicRel δ {0, 1}) : γ 0 = δ 0 := by
  obtain ⟨H⟩ := h
  have hmem : (0 : I) ∈ ({0, 1} : Set I) := by left; rfl
  rw [← H.eq_fst 1 hmem, H.apply_one 0]

/-- **Homotopy invariance of the displacement.**  If two paths are homotopic
relative to their endpoints, they have the same displacement.  This is the core
mechanism by which the winding invariant kills boundaries: the boundary loop of a
singular `2`-simplex is null-homotopic in the contractible standard simplex, so
its displacement vanishes. -/
theorem pathDisplacement_homotopic {γ δ : C(I, SphereOne)}
    (h : γ.HomotopicRel δ {0, 1}) : pathDisplacement γ = pathDisplacement δ := by
  have hend : γ 0 = δ 0 := homotopicRel_apply_zero h
  have he_γ : γ 0 = trigCirclePoint (pathLiftStart γ) := (pathLiftStart_spec γ).symm
  have he_δ : δ 0 = trigCirclePoint (pathLiftStart γ) := by rw [← hend]; exact he_γ
  have key : isCoveringMap_trig.liftPath γ (pathLiftStart γ) he_γ 1
      = isCoveringMap_trig.liftPath δ (pathLiftStart γ) he_δ 1 :=
    isCoveringMap_trig.liftPath_apply_one_eq_of_homotopicRel h (pathLiftStart γ) he_γ he_δ
  have dγ : pathDisplacement γ
      = isCoveringMap_trig.liftPath γ (pathLiftStart γ) he_γ 1 - pathLiftStart γ := by
    rw [pathDisplacement_eq γ (isCoveringMap_trig.liftPath γ (pathLiftStart γ) he_γ)
        (isCoveringMap_trig.liftPath_lifts γ (pathLiftStart γ) he_γ),
      isCoveringMap_trig.liftPath_zero γ (pathLiftStart γ) he_γ]
  have dδ : pathDisplacement δ
      = isCoveringMap_trig.liftPath δ (pathLiftStart γ) he_δ 1 - pathLiftStart γ := by
    rw [pathDisplacement_eq δ (isCoveringMap_trig.liftPath δ (pathLiftStart γ) he_δ)
        (isCoveringMap_trig.liftPath_lifts δ (pathLiftStart γ) he_δ),
      isCoveringMap_trig.liftPath_zero δ (pathLiftStart γ) he_δ]
  rw [dγ, dδ, key]

/-- **Additivity of the displacement under path concatenation.**  The
displacement of a concatenated path is the sum of the displacements.  Together
with homotopy invariance this is exactly what makes the winding number a homology
invariant: the alternating face sum of a singular `2`-simplex telescopes to `0`. -/
theorem pathDisplacement_trans {x y z : SphereOne} (γ : Path x y) (γ' : Path y z) :
    pathDisplacement ((γ.trans γ' : Path x z) : C(I, SphereOne))
      = pathDisplacement (γ : C(I, SphereOne)) + pathDisplacement (γ' : C(I, SphereOne)) := by
  obtain ⟨e, he⟩ := trigCirclePoint_surjective x
  have hpe : x = trigCirclePoint e := he.symm
  have hγ0 : (γ : C(I, SphereOne)) 0 = trigCirclePoint e := γ.source.trans hpe
  set Lγ := isCoveringMap_trig.liftPath (γ : C(I, SphereOne)) e hγ0 with hLγ
  have hLγlifts : trigCirclePoint ∘ (Lγ : I → ℝ) = (γ : C(I, SphereOne)) :=
    isCoveringMap_trig.liftPath_lifts (γ : C(I, SphereOne)) e hγ0
  have hLγ0 : Lγ 0 = e := isCoveringMap_trig.liftPath_zero (γ : C(I, SphereOne)) e hγ0
  have htrigLγ1 : trigCirclePoint (Lγ 1) = y := by
    have := congrFun hLγlifts 1
    rw [Function.comp_apply] at this
    rw [this]; exact γ.target
  have hγ'0 : (γ' : C(I, SphereOne)) 0 = trigCirclePoint (Lγ 1) := by
    rw [htrigLγ1]; exact γ'.source
  set Lγ' := isCoveringMap_trig.liftPath (γ' : C(I, SphereOne)) (Lγ 1) hγ'0 with hLγ'
  have hLγ'0 : Lγ' 0 = Lγ 1 :=
    isCoveringMap_trig.liftPath_zero (γ' : C(I, SphereOne)) (Lγ 1) hγ'0
  -- displacement of the two pieces
  have hd_γ : pathDisplacement (γ : C(I, SphereOne)) = Lγ 1 - e := by
    rw [pathDisplacement_eq (γ : C(I, SphereOne)) Lγ hLγlifts, hLγ0]
  have hd_γ' : pathDisplacement (γ' : C(I, SphereOne)) = Lγ' 1 - Lγ 1 := by
    rw [pathDisplacement_eq (γ' : C(I, SphereOne)) Lγ'
        (isCoveringMap_trig.liftPath_lifts (γ' : C(I, SphereOne)) (Lγ 1) hγ'0), hLγ'0]
  -- displacement of the concatenation, via the lift-of-concatenation theorem
  have htrans0 : ((γ.trans γ' : Path x z) : C(I, SphereOne)) 0 = trigCirclePoint e :=
    (γ.trans γ').source.trans hpe
  set Lt := isCoveringMap_trig.liftPath ((γ.trans γ' : Path x z) : C(I, SphereOne)) e htrans0
    with hLt
  have hLtlifts : trigCirclePoint ∘ (Lt : I → ℝ) = ((γ.trans γ' : Path x z) : C(I, SphereOne)) :=
    isCoveringMap_trig.liftPath_lifts ((γ.trans γ' : Path x z) : C(I, SphereOne)) e htrans0
  have hLt0 : Lt 0 = e :=
    isCoveringMap_trig.liftPath_zero ((γ.trans γ' : Path x z) : C(I, SphereOne)) e htrans0
  have hLt1 : Lt 1 = Lγ' 1 := by
    have h := DFunLike.congr_fun (isCoveringMap_trig.liftPath_trans hpe γ γ') 1
    simpa using h
  have hd_trans : pathDisplacement ((γ.trans γ' : Path x z) : C(I, SphereOne)) = Lγ' 1 - e := by
    rw [pathDisplacement_eq ((γ.trans γ' : Path x z) : C(I, SphereOne)) Lt hLtlifts, hLt0, hLt1]
  rw [hd_trans, hd_γ, hd_γ']; ring

/-- The winding number of a path: displacement normalized by one full turn. -/
def pathWinding (γ : C(I, SphereOne)) : ℝ :=
  pathDisplacement γ / (2 * Real.pi)

/-- A closed path has displacement equal to an integer number of full turns. -/
theorem pathDisplacement_loop_intMul (γ : C(I, SphereOne)) (hloop : γ 1 = γ 0) :
    ∃ k : ℤ, pathDisplacement γ = (k : ℝ) * (2 * Real.pi) := by
  have hfib : trigCirclePoint (pathLift γ 1) = trigCirclePoint (pathLift γ 0) := by
    have h1 : trigCirclePoint (pathLift γ 1) = γ 1 := congrFun (pathLift_lifts γ) 1
    have h0 : trigCirclePoint (pathLift γ 0) = γ 0 := congrFun (pathLift_lifts γ) 0
    rw [h1, h0, hloop]
  obtain ⟨k, hk⟩ := (trigCirclePoint_eq_iff (pathLift γ 1) (pathLift γ 0)).1 hfib
  refine ⟨k, ?_⟩
  rw [pathDisplacement_self, hk]
  ring

/-- A closed path has integer winding. -/
theorem pathWinding_loop_integral (γ : C(I, SphereOne)) (hloop : γ 1 = γ 0) :
    ∃ k : ℤ, pathWinding γ = (k : ℝ) := by
  obtain ⟨k, hk⟩ := pathDisplacement_loop_intMul γ hloop
  refine ⟨k, ?_⟩
  rw [pathWinding, hk]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp [hpi]

/-- The fundamental once-around loop, as a path `I → TopCat.sphere 1`. -/
def fundamentalLoop : C(I, SphereOne) where
  toFun t := trigCirclePoint (2 * Real.pi * (t : ℝ))
  continuous_toFun :=
    continuous_trigCirclePoint.comp (continuous_const.mul continuous_subtype_val)

/-- The explicit linear lift `t ↦ 2π t` of the fundamental loop. -/
def fundamentalLift : C(I, ℝ) where
  toFun t := 2 * Real.pi * (t : ℝ)
  continuous_toFun := continuous_const.mul continuous_subtype_val

theorem fundamentalLift_lifts :
    trigCirclePoint ∘ (fundamentalLift : I → ℝ) = fundamentalLoop := rfl

/-- **The displacement of the fundamental loop is one full turn `2π`.**  This is
the surjectivity witness for the winding invariant: the canonical generator maps
to a nonzero value. -/
theorem pathDisplacement_fundamentalLoop :
    pathDisplacement fundamentalLoop = 2 * Real.pi := by
  rw [pathDisplacement_eq fundamentalLoop fundamentalLift fundamentalLift_lifts]
  show 2 * Real.pi * ((1 : I) : ℝ) - 2 * Real.pi * ((0 : I) : ℝ) = 2 * Real.pi
  simp

/-- **The winding number of the fundamental loop is `1`.**  The winding invariant
is therefore a left inverse to the fundamental loop class on the nose: it sends
the canonical generator to `1`. -/
theorem pathWinding_fundamentalLoop : pathWinding fundamentalLoop = 1 := by
  rw [pathWinding, pathDisplacement_fundamentalLoop]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp

/-- Zero winding forces the canonical lift endpoints to agree.  This is the
lift-level form consumed by the singular cone construction in
`CircleWindingChain`. -/
theorem pathLift_endpoint_eq_of_winding_zero (γ : C(I, SphereOne))
    (hw : pathWinding γ = 0) :
    pathLift γ 1 = pathLift γ 0 := by
  have hdisp : pathDisplacement γ = 0 := by
    unfold pathWinding at hw
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    rcases (div_eq_zero_iff).mp hw with hzero | hden
    · exact hzero
    · exact False.elim (hpi hden)
  rw [pathDisplacement_self] at hdisp
  linarith

/-- The canonical lift of any interval path is uniformly bounded.  This compactness
fact is the analytic input needed for the apex continuity of the singular cone. -/
theorem pathLift_exists_norm_bound (γ : C(I, SphereOne)) :
    ∃ C : ℝ, ∀ t : I, ‖pathLift γ t‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (s := (Set.univ : Set I)) (f := fun t : I => pathLift γ t)
    (by exact (pathLift γ).continuous.continuousOn)
  refine ⟨C, ?_⟩
  intro t
  exact hC t (by simp)

/-- The canonical lift, shifted by its initial value, is uniformly bounded.  This
is the exact bound consumed by the cone formula
`L₀ + (1 - x₂) * (L(coneBaseParam x) - L₀)`. -/
theorem pathLift_shifted_exists_norm_bound (γ : C(I, SphereOne)) :
    ∃ C : ℝ, ∀ t : I, ‖pathLift γ t - pathLift γ 0‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (s := (Set.univ : Set I)) (f := fun t : I => pathLift γ t - pathLift γ 0)
    (by exact ((pathLift γ).continuous.sub continuous_const).continuousOn)
  refine ⟨C, ?_⟩
  intro t
  exact hC t (by simp)

/-- A closed path in `S¹` with zero winding is homotopic rel endpoints to the
constant path at its basepoint.  The homotopy lifts the path to `ℝ`, uses zero
winding to identify the lift endpoints, and contracts the lifted path linearly
to its initial value before projecting back through the covering map. -/
theorem pathHomotopicRel_const_of_loop_winding_zero (γ : C(I, SphereOne))
    (hloop : γ 1 = γ 0) (hw : pathWinding γ = 0) :
    γ.HomotopicRel (ContinuousMap.const I (γ 0)) {0, 1} := by
  have hlift_end : pathLift γ 1 = pathLift γ 0 := by
    exact pathLift_endpoint_eq_of_winding_zero γ hw
  let Hmap : C(I × I, SphereOne) := {
    toFun p :=
      trigCirclePoint
        ((1 - ((p.1 : I) : ℝ)) * pathLift γ p.2 +
          ((p.1 : I) : ℝ) * pathLift γ 0)
    continuous_toFun := by
      exact continuous_trigCirclePoint.comp (by continuity)
  }
  let H : γ.Homotopy (ContinuousMap.const I (γ 0)) :=
    ContinuousMap.Homotopy.mk Hmap
      (by
        intro x
        change trigCirclePoint
            ((1 - (((0 : I) : I) : ℝ)) * pathLift γ x +
              (((0 : I) : I) : ℝ) * pathLift γ 0) = γ x
        simp
        exact congrFun (pathLift_lifts γ) x)
      (by
        intro x
        change trigCirclePoint
            ((1 - (((1 : I) : I) : ℝ)) * pathLift γ x +
              (((1 : I) : I) : ℝ) * pathLift γ 0) =
            (ContinuousMap.const I (γ 0)) x
        simp
        exact congrFun (pathLift_lifts γ) 0)
  refine ⟨ContinuousMap.HomotopyWith.mk H ?_⟩
  intro t x hx
  rcases hx with hx | hx
  · subst x
    change trigCirclePoint
        ((1 - ((t : I) : ℝ)) * pathLift γ 0 +
          ((t : I) : ℝ) * pathLift γ 0) = γ 0
    rw [← congrFun (pathLift_lifts γ) 0]
    congr 1
    ring
  · subst x
    change trigCirclePoint
        ((1 - ((t : I) : ℝ)) * pathLift γ 1 +
          ((t : I) : ℝ) * pathLift γ 0) = γ 1
    rw [hlift_end]
    rw [hloop]
    rw [← congrFun (pathLift_lifts γ) 0]
    congr 1
    ring

end

end CircleWinding
end Foundation
end IndisputableMonolith
