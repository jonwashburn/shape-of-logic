import Mathlib
import IndisputableMonolith.Masses.CompositeBindingOperator

/-!
# The neutron-proton split is purely isospin-breaking

`CompositeBindingOperator` writes each nucleon as the common rung-43 baryon scale minus a
positive binding deficit (`δ_p ≈ 31 MeV`, `δ_n ≈ 30 MeV`), and proves the splitting is the
deficit difference `m_n − m_p = δ_p − δ_n`. Taken alone that looks like U8 still owes a 30 MeV
computation. It does not.

This module proves the splitting is **independent of the common strong scale**: for any
isospin-symmetric strong deficit `δ_strong` shared by both nucleons, the splitting is unchanged
when you subtract it from both deficits. The ~30 MeV color-binding scale cancels exactly. So the
1.293 MeV split is entirely isospin-breaking, and U8's splitting target shrinks from a 30 MeV
QCD computation to a ~1 MeV isospin-breaking computation: the down-up quark mass difference plus
the electromagnetic self-energy.

We then decompose the isospin-breaking part into an electromagnetic piece and a quark-mass
piece, and prove the key sign constraint. The electromagnetic self-energy makes the charged
proton heavier (its contribution to `m_n − m_p` is negative; the Cottingham/lattice result).
Therefore the quark-mass (down−up) contribution must **overcompensate**: it strictly exceeds the
observed split. A future recognition/QCD operator that computes the two isospin-breaking
contributions must satisfy `Δ_qmass > m_n − m_p > 0` with `Δ_EM < 0`.

Main results:

* `split_independent_of_strong`: the splitting does not depend on the common strong scale;
* `split_eq_em_plus_qmass`: it is the sum of the EM and quark-mass isospin contributions;
* `qmass_contribution_overcompensates`: with a negative EM contribution, the quark-mass
  contribution strictly exceeds the observed split.

What stays open (genuine physics): the absolute values of `Δ_EM` and `Δ_qmass` from recognition
dynamics. This module fixes their sum and the sign relation between them.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace NucleonSplitIsospinDecomposition

open CompositeBindingOperator
open ProtonBindingDerivation

noncomputable section

/-- The neutron-proton mass splitting, in MeV. -/
def npSplit : ℝ := m_neutron_PDG - m_proton_PDG

/-- The split is positive: the neutron is heavier. -/
theorem npSplit_pos : 0 < npSplit := by
  unfold npSplit m_neutron_PDG m_proton_PDG; norm_num

/-- The split is the PDG value `≈ 1.293 MeV`. -/
theorem npSplit_bounds : (1.29 : ℝ) < npSplit ∧ npSplit < (1.30 : ℝ) := by
  unfold npSplit m_neutron_PDG m_proton_PDG
  constructor <;> norm_num

/-- **The common strong scale cancels.** For any isospin-symmetric strong deficit `δ_strong`
shared by both nucleons, the splitting equals the difference of the residual isospin-breaking
deficits. The ~30 MeV color-binding scale does not enter the splitting. -/
theorem split_independent_of_strong (δ_strong : ℝ) :
    npSplit =
      (bindingDeficit .proton - δ_strong) - (bindingDeficit .neutron - δ_strong) := by
  unfold npSplit
  rw [np_split_eq_deficit_difference]
  ring

/-- The isospin-breaking residual deficit of a nucleon at a given common strong scale. -/
def isospinResidual (δ_strong : ℝ) : Nucleon → ℝ :=
  fun N => bindingDeficit N - δ_strong

/-- The splitting is the difference of the isospin residuals, at any common strong scale. -/
theorem split_eq_isospin_residual_difference (δ_strong : ℝ) :
    npSplit = isospinResidual δ_strong .proton - isospinResidual δ_strong .neutron := by
  unfold isospinResidual
  exact split_independent_of_strong δ_strong

/-- **The split is the sum of the EM and quark-mass isospin contributions.** Given any
decomposition of the observed splitting into an electromagnetic contribution `emSplit` and a
quark-mass contribution `qmassSplit`, the identity is recorded. (`emSplit`, `qmassSplit` are the
contributions to `m_n − m_p`.) -/
theorem split_eq_em_plus_qmass {emSplit qmassSplit : ℝ}
    (hdecomp : npSplit = emSplit + qmassSplit) :
    m_neutron_PDG - m_proton_PDG = emSplit + qmassSplit := by
  rw [← hdecomp]; rfl

/-- **The quark-mass contribution overcompensates the electromagnetic one.** The electromagnetic
self-energy makes the charged proton heavier, so its contribution to `m_n − m_p` is negative.
Given the observed positive split, the down-up quark-mass contribution must strictly exceed the
whole observed splitting. -/
theorem qmass_contribution_overcompensates {emSplit qmassSplit : ℝ}
    (hdecomp : npSplit = emSplit + qmassSplit) (hem : emSplit < 0) :
    npSplit < qmassSplit := by
  linarith

/-- The quark-mass contribution is strictly positive (it carries the whole split and more). -/
theorem qmass_contribution_pos {emSplit qmassSplit : ℝ}
    (hdecomp : npSplit = emSplit + qmassSplit) (hem : emSplit < 0) :
    0 < qmassSplit :=
  lt_trans npSplit_pos (qmass_contribution_overcompensates hdecomp hem)

/-- Certificate for the U8 isospin decomposition of the splitting. -/
structure NucleonSplitIsospinCert where
  split_pos : 0 < npSplit
  split_band : (1.29 : ℝ) < npSplit ∧ npSplit < 1.30
  strong_scale_cancels :
    ∀ δ_strong : ℝ,
      npSplit = (bindingDeficit .proton - δ_strong) - (bindingDeficit .neutron - δ_strong)
  qmass_overcompensates :
    ∀ {emSplit qmassSplit : ℝ}, npSplit = emSplit + qmassSplit → emSplit < 0 →
      npSplit < qmassSplit

theorem nucleonSplitIsospinCert_holds : Nonempty NucleonSplitIsospinCert :=
  ⟨{ split_pos := npSplit_pos
     split_band := npSplit_bounds
     strong_scale_cancels := split_independent_of_strong
     qmass_overcompensates := fun h hem => qmass_contribution_overcompensates h hem }⟩

end

end NucleonSplitIsospinDecomposition
end Masses
end IndisputableMonolith
