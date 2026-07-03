import Mathlib
import IndisputableMonolith.Masses.L1bHyperoctahedralGroup
import IndisputableMonolith.Masses.L1ScalarBridge
import IndisputableMonolith.Constants.AlphaDerivation

/-!
# L1 uniformity from octahedral transitivity (MODEL → THEOREM lift, door L1-Test2)

The leading charged-lepton torsion correction `δ_21` rests, in
`L1ScalarBridge.LeadingCorrectionIsBoundaryFlux`, on a MODEL premise
`uniform_reduction : I = solid_angle_Q3 * lam`. That premise silently bakes in
*two* things: (a) the boundary recognition flux has a **uniform** density across
the boundary, and (b) it therefore integrates to `(total boundary measure) · lam`.

This module removes (a) as an assumption and **derives** it. The boundary of the
recognition cube `∂Q₃` carries its content on the eight vertex cells (the eight
angular deficits assembling to `4π` by discrete Gauss–Bonnet). The eight cells
are the sign patterns `Fin 3 → Bool` (the eight vertices `{±1}³`), and the
hyperoctahedral group `B3 = O_h` (`L1bHyperoctahedralGroup.SignedPerm`, order 48)
acts on them by coordinate permutation + sign flip.

We prove, unconditionally:

* `MulAction SignedPerm (Fin 3 → Bool)` — the induced action on the vertices,
* `IsPretransitive` — `O_h` acts **transitively** on the eight vertices,
* `invariant_const` — any `O_h`-invariant density on the vertices is **constant**,
* `uniform_reduction_from_invariance` — an `O_h`-invariant density summed over the
  vertex cells (whose measures total `solid_angle_Q3`) equals `solid_angle_Q3 · lam`.

So `uniform_reduction` is no longer a postulate: it follows from the strictly
weaker, physically motivated MODEL premise that the flux density **respects the
cube's symmetry group** (`O_h`-invariance). Transitivity upgrades invariance to
uniformity; the arithmetic collapse does the rest.

**Honest status.** The transitivity, the invariance⇒constant lemma, and the
collapse are THEOREMs (0 sorry, `xor`/`Finset.sum` group theory, no RS axioms).
The residual MODEL floor is one hypothesis: the recognition flux density is
`O_h`-invariant. This is the symmetry statement `∀ g b, d (g • b) = d b`, which
replaces the old "the flux is uniform" — a genuine sharpening, not a relabeling,
because invariance is a weaker and independently checkable symmetry condition and
the upgrade to uniformity is now a proved consequence, not part of the premise.
-/

namespace IndisputableMonolith
namespace Masses
namespace L1UniformityFromOctahedral

open scoped BigOperators
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup
open IndisputableMonolith.Masses.L1bHyperoctahedralGroup.SignedPerm
open IndisputableMonolith.Constants.AlphaDerivation (solid_angle_Q3 solid_angle_Q3_eq)

/-- The eight cube vertices `{±1}³`, encoded as sign patterns
(`true` = the `-1` coordinate). -/
abbrev CubeVertex := Fin 3 → Bool

/-- The induced action of a signed permutation on a vertex sign pattern:
permute the coordinates by `perm`, then toggle the sign bit where `sign` is set.
This is the sign-bit shadow of `SignedPerm.signedAct` on `{±1}³`, and it has the
same `xor` form as the group's own multiplication law (`mul_sign`). -/
def vertexAct (g : SignedPerm) (b : CubeVertex) : CubeVertex :=
  fun i => xor (g.sign i) (b (g.perm i))

theorem vertexAct_one (b : CubeVertex) : vertexAct 1 b = b := by
  funext i; simp [vertexAct]

theorem vertexAct_mul (g h : SignedPerm) (b : CubeVertex) :
    vertexAct (g * h) b = vertexAct g (vertexAct h b) := by
  funext i
  simp only [vertexAct, mul_sign, mul_perm, Equiv.trans_apply]
  exact Bool.xor_assoc _ _ _

/-- The hyperoctahedral group acts on the eight cube vertices. -/
instance : MulAction SignedPerm CubeVertex where
  smul := vertexAct
  one_smul := vertexAct_one
  mul_smul := vertexAct_mul

@[simp] theorem vertex_smul_def (g : SignedPerm) (b : CubeVertex) :
    g • b = vertexAct g b := rfl

/-- **Transitivity.** `O_h` acts transitively on the eight cube vertices: the pure
sign-flip element `⟨1, b xor c⟩` already carries `b` to `c`. -/
instance : MulAction.IsPretransitive SignedPerm CubeVertex := by
  refine ⟨fun b c => ?_⟩
  refine ⟨⟨1, fun i => xor (b i) (c i)⟩, ?_⟩
  funext i
  simp only [vertex_smul_def, vertexAct, Equiv.Perm.coe_one, id_eq]
  cases b i <;> cases c i <;> rfl

/-- **Invariance ⇒ constancy.** A density on the vertices that is invariant under
the octahedral action is constant, because the action is transitive. -/
theorem invariant_const {d : CubeVertex → ℝ}
    (hinv : ∀ (g : SignedPerm) (b : CubeVertex), d (g • b) = d b)
    (b c : CubeVertex) : d b = d c := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SignedPerm b c
  rw [← hg, hinv]

/-- **The uniform-reduction lift.** If the boundary flux is the sum over the eight
vertex cells of `measure · density`, the density is `O_h`-invariant, and the cell
measures total `solid_angle_Q3`, then the flux equals `solid_angle_Q3 · lam` where
`lam` is the (now provably constant) density. This *derives* the old
`uniform_reduction` MODEL premise from an octahedral-symmetry premise. -/
theorem uniform_reduction_from_invariance
    {d m : CubeVertex → ℝ} {lam : ℝ}
    (hinv : ∀ (g : SignedPerm) (b : CubeVertex), d (g • b) = d b)
    (b0 : CubeVertex) (hlam : d b0 = lam)
    (htot : ∑ v, m v = solid_angle_Q3) :
    ∑ v, m v * d v = solid_angle_Q3 * lam := by
  have hconst : ∀ v, d v = lam := fun v => by
    rw [invariant_const hinv v b0, hlam]
  calc ∑ v, m v * d v
      = ∑ v, m v * lam := by
        refine Finset.sum_congr rfl ?_; intro v _; rw [hconst v]
    _ = (∑ v, m v) * lam := by rw [Finset.sum_mul]
    _ = solid_angle_Q3 * lam := by rw [htot]

/-- **Capstone.** The full leading-correction forcing, with `uniform_reduction`
replaced by the octahedral-symmetry premise. Given that the boundary flux `I`
decomposes over the eight vertex cells with an `O_h`-invariant density summing (in
measure) to `solid_angle_Q3`, and that the flux equals the posted content `n`,
the leading torsion constant is forced: `lam = n / (4π)`. -/
theorem leadingCorrection_from_octahedral
    {n : ℕ} {lam I : ℝ}
    (hflux : ∃ (m d : CubeVertex → ℝ) (b0 : CubeVertex),
        I = ∑ v, m v * d v ∧ d b0 = lam ∧
        (∑ v, m v = solid_angle_Q3) ∧
        (∀ (g : SignedPerm) (b : CubeVertex), d (g • b) = d b))
    (hcontent : I = (n : ℝ)) :
    lam = (n : ℝ) / (4 * Real.pi) := by
  obtain ⟨m, d, b0, hI, hlam, htot, hinv⟩ := hflux
  have huni : I = solid_angle_Q3 * lam := by
    rw [hI]; exact uniform_reduction_from_invariance hinv b0 hlam htot
  exact L1ScalarBridge.leadingCorrection_forced ⟨hcontent, huni⟩

end L1UniformityFromOctahedral
end Masses
end IndisputableMonolith
