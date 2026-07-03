import Mathlib

namespace IndisputableMonolith
namespace VoxelWalks

noncomputable section
open Real

def phi : ℝ := (1 + Real.sqrt 5) / 2

def A2 (P γ : ℝ) : ℝ := P * (phi) ^ (-(2 * γ))

def sigmaCore (n : ℕ) (a2 : ℝ) : ℝ :=
  let num := (3 : ℝ) ^ n * (a2) ^ n
  let den := 2 * (1 - 2 * a2) ^ (2 * n - 1)
  num / den

@[simp] lemma sigmaCore_n0 (a2 : ℝ) : sigmaCore 0 a2 = 1 / 2 := by
  unfold sigmaCore
  simp

def fEye (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n
def fHalfVoxel (n : ℕ) : ℝ := ((23 : ℝ) / 24) ^ n
def fFace (n : ℕ) : ℝ := ((11 : ℝ) / 12) ^ n

def sigmaN (n : ℕ) (a2 : ℝ)
  (useEye : Bool := true) (useHalfVoxel : Bool := true) (useFace : Bool := false) : ℝ :=
  let core := sigmaCore n a2
  let eye := if useEye then fEye n else 1
  let hv  := if useHalfVoxel then fHalfVoxel n else 1
  let face := if useFace then fFace n else 1
  core * eye * hv * face

def A2_QED : ℝ := A2 ((1 : ℝ) / 18) ((2 : ℝ) / 3)
def A2_QCD : ℝ := A2 ((2 : ℝ) / 9) ((2 : ℝ) / 3)

def convergent (a2 : ℝ) : Prop := 1 - 2 * a2 > 0

lemma sigmaN_QED_expand (n : ℕ) :
  sigmaN n A2_QED true true false =
    sigmaCore n A2_QED * ((1 / 2 : ℝ) ^ n) * (((23 : ℝ) / 24) ^ n) := by
  unfold sigmaN fEye fHalfVoxel fFace
  simp

lemma sigmaN_QCD_expand (n : ℕ) :
  sigmaN n A2_QCD true true false =
    sigmaCore n A2_QCD * ((1 / 2 : ℝ) ^ n) * (((23 : ℝ) / 24) ^ n) := by
  unfold sigmaN fEye fHalfVoxel fFace
  simp

end

end VoxelWalks
end IndisputableMonolith
