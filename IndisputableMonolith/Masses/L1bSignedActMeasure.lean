import Mathlib
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup

/-!
# `signedAct` is volume-preserving

Each signed permutation acts on `Fin 3 → ℝ` by a coordinate permutation
followed by per-coordinate sign flips, both of which are Lebesgue
measure-preserving.  We decompose `signedAct g = signMap g ∘ permMap g` and
compose the two measure-preserving factors.  This supplies the
`SMulInvariantMeasure` hypothesis needed by the abstract tile-measure identity
`L1bChamberMeasure.tile_measure_of_card48`.
-/

namespace IndisputableMonolith.Masses.L1bSignedActMeasure

open MeasureTheory
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup.SignedPerm

/-- The coordinate-permutation factor of `signedAct g`. -/
def permMap (g : SignedPerm) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) g.perm.symm)

/-- The sign-flip factor of `signedAct g`. -/
def signMap (g : SignedPerm) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun a i => if g.sign i then -(a i) else a i

theorem permMap_apply (g : SignedPerm) (v : Fin 3 → ℝ) (a : Fin 3) :
    permMap g v a = v (g.perm a) := by
  show (MeasurableEquiv.piCongrLeft (fun _ : Fin 3 => ℝ) g.perm.symm) v a = v (g.perm a)
  rw [MeasurableEquiv.coe_piCongrLeft]
  have h := Equiv.piCongrLeft_apply_apply (fun _ : Fin 3 => ℝ) g.perm.symm v (g.perm.symm.symm a)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_symm]

theorem signedAct_eq (g : SignedPerm) :
    signedAct g = signMap g ∘ permMap g := by
  funext v i
  simp only [Function.comp_apply, signMap, signedAct]
  rw [permMap_apply]

theorem measurePreserving_permMap (g : SignedPerm) :
    MeasurePreserving (permMap g) (volume : Measure (Fin 3 → ℝ)) volume := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin 3 => (volume : Measure ℝ)) g.perm.symm
  rw [volume_pi]
  exact h

theorem measurePreserving_signMap (g : SignedPerm) :
    MeasurePreserving (signMap g) (volume : Measure (Fin 3 → ℝ)) volume := by
  have h : ∀ i : Fin 3,
      MeasurePreserving (fun x : ℝ => if g.sign i then -x else x) volume volume := by
    intro i
    rcases hb : g.sign i with _ | _
    · simp only [Bool.false_eq_true, if_false]
      exact MeasurePreserving.id volume
    · simp only [if_true]
      exact Measure.measurePreserving_neg volume
  have hpi := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure ℝ))
    (fun _ : Fin 3 => (volume : Measure ℝ)) h
  rw [volume_pi]
  exact hpi

theorem measurePreserving_signedAct (g : SignedPerm) :
    MeasurePreserving (signedAct g) (volume : Measure (Fin 3 → ℝ)) volume := by
  rw [signedAct_eq]
  exact (measurePreserving_signMap g).comp (measurePreserving_permMap g)

end IndisputableMonolith.Masses.L1bSignedActMeasure
