import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Masses.ProtonBindingDerivation

/-!
# Composite Binding Operator

U8 should not be closed by comparing proton and neutron masses directly to current-quark
MS-bar masses. The current quark masses are a tiny part of nucleon inertia; visible matter is
mostly binding. This module formalizes the correct operator surface:

* a color-neutral nucleon starts at the common rung-43 baryon scale `φ^43 / 10^6`;
* a positive sub-rung binding deficit lowers that scale to the observed proton/neutron mass;
* the neutron-proton mass splitting is the difference of two sub-rung deficits, not a rung jump.

This still does not derive the deficits dynamically from confinement. It makes the missing
object exact: a future recognition/QCD-like composite operator must compute the two deficits
`δ_p` and `δ_n` in the 30 MeV band, with `δ_p - δ_n = m_n - m_p`.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace CompositeBindingOperator

open Constants
open ProtonBindingDerivation

noncomputable section

/-- The two nucleons tracked by the first composite-binding target. -/
inductive Nucleon where
  | proton
  | neutron
  deriving DecidableEq, Repr

/-- Current-quark valence content of a nucleon. -/
structure ValenceContent where
  nUp : ℕ
  nDown : ℕ
  baryonNumberClosed : nUp + nDown = 3
deriving Repr

/-- Proton valence content: `uud`. -/
def protonValence : ValenceContent where
  nUp := 2
  nDown := 1
  baryonNumberClosed := by decide

/-- Neutron valence content: `udd`. -/
def neutronValence : ValenceContent where
  nUp := 1
  nDown := 2
  baryonNumberClosed := by decide

/-- The common rung-43 baryon scale, in MeV. -/
def rung43Mass : ℝ := phi ^ (43 : ℕ) / 1000000

/-- PDG nucleon mass, in MeV. -/
def pdgMass : Nucleon → ℝ
  | .proton => m_proton_PDG
  | .neutron => m_neutron_PDG

/-- Valence current-quark mass sum, using the same PDG inputs as
`ProtonBindingDerivation`. -/
def valenceMass : Nucleon → ℝ
  | .proton => 2 * m_u_PDG + m_d_PDG
  | .neutron => m_u_PDG + 2 * m_d_PDG

/-- The positive binding deficit that lowers the common rung-43 baryon scale to the observed
nucleon mass. This is the quantity a future dynamic composite operator must derive. -/
def bindingDeficit : Nucleon → ℝ
  | Nucleon.proton => rung43Mass - m_proton_PDG
  | Nucleon.neutron => rung43Mass - m_neutron_PDG

/-- The composite mass reconstructed from the common rung and a binding deficit. -/
def compositeMass (N : Nucleon) : ℝ :=
  rung43Mass - bindingDeficit N

theorem compositeMass_proton_eq_pdg :
    compositeMass .proton = m_proton_PDG := by
  simp [compositeMass, bindingDeficit]

theorem compositeMass_neutron_eq_pdg :
    compositeMass .neutron = m_neutron_PDG := by
  simp [compositeMass, bindingDeficit]

theorem bindingDeficit_proton_pos : 0 < bindingDeficit .proton := by
  unfold bindingDeficit rung43Mass
  exact sub_pos.mpr proton_below_rung43

theorem bindingDeficit_neutron_pos : 0 < bindingDeficit .neutron := by
  unfold bindingDeficit rung43Mass
  exact sub_pos.mpr neutron_below_rung43

/-- The proton binding deficit is in the 30-33 MeV band. -/
theorem proton_deficit_30_33MeV :
    (30 : ℝ) < bindingDeficit .proton ∧ bindingDeficit .proton < (33 : ℝ) := by
  unfold bindingDeficit rung43Mass m_proton_PDG
  rw [show phi = Real.goldenRatio from rfl]
  constructor
  · rw [lt_sub_iff_add_lt]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    linarith [Numerics.phi_pow43_gt]
  · rw [sub_lt_iff_lt_add]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    linarith [Numerics.phi_pow43_lt]

/-- The neutron binding deficit is in the 29-31 MeV band. -/
theorem neutron_deficit_29_31MeV :
    (29 : ℝ) < bindingDeficit .neutron ∧ bindingDeficit .neutron < (31 : ℝ) := by
  unfold bindingDeficit rung43Mass m_neutron_PDG
  rw [show phi = Real.goldenRatio from rfl]
  constructor
  · rw [lt_sub_iff_add_lt]
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    linarith [Numerics.phi_pow43_gt]
  · rw [sub_lt_iff_lt_add]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    linarith [Numerics.phi_pow43_lt]

/-- The neutron valence current-quark fraction is below 2%; binding dominates the neutron too. -/
theorem neutron_valence_fraction_lt_2pct :
    valenceMass .neutron / m_neutron_PDG < (0.02 : ℝ) := by
  unfold valenceMass m_neutron_PDG m_u_PDG m_d_PDG
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 939.565)]
  norm_num

/-- The neutron binding energy (mass minus valence current masses) exceeds 98% of the neutron mass. -/
theorem neutron_binding_dominance :
    m_neutron_PDG - valenceMass .neutron > (0.98 : ℝ) * m_neutron_PDG := by
  unfold valenceMass m_neutron_PDG m_u_PDG m_d_PDG
  norm_num

/-- The proton binding deficit is larger than the neutron binding deficit. The neutron is heavier
because its deficit from the common rung-43 scale is smaller. -/
theorem proton_deficit_gt_neutron_deficit :
    bindingDeficit .neutron < bindingDeficit .proton := by
  unfold bindingDeficit m_proton_PDG m_neutron_PDG
  norm_num

/-- The neutron-proton mass splitting is exactly the proton-neutron deficit difference. This is
the algebraic target a dynamic isospin/EM binding operator must derive. -/
theorem np_split_eq_deficit_difference :
    m_neutron_PDG - m_proton_PDG =
      bindingDeficit .proton - bindingDeficit .neutron := by
  unfold bindingDeficit
  ring

/-- The deficit difference is sub-rung, inherited from `ProtonBindingDerivation.np_split_subrung`. -/
theorem deficit_difference_subrung :
    (bindingDeficit .proton - bindingDeficit .neutron)
        / (phi ^ (43 : ℕ) / 1000000 - phi ^ (42 : ℕ) / 1000000) < 0.004 := by
  rw [← np_split_eq_deficit_difference]
  exact np_split_subrung

/-- The composite-binding certificate packages the closed operator surface. -/
structure CompositeBindingOperatorCert where
  proton_reproduced : compositeMass .proton = m_proton_PDG
  neutron_reproduced : compositeMass .neutron = m_neutron_PDG
  proton_deficit_pos : 0 < bindingDeficit .proton
  neutron_deficit_pos : 0 < bindingDeficit .neutron
  proton_deficit_band : (30 : ℝ) < bindingDeficit .proton ∧ bindingDeficit .proton < 33
  neutron_deficit_band : (29 : ℝ) < bindingDeficit .neutron ∧ bindingDeficit .neutron < 31
  proton_valence_negligible : valenceMass .proton / m_proton_PDG < 0.01
  neutron_valence_negligible : valenceMass .neutron / m_neutron_PDG < 0.02
  neutron_binding_dominates :
    m_neutron_PDG - valenceMass .neutron > (0.98 : ℝ) * m_neutron_PDG
  np_split_is_deficit_difference :
    m_neutron_PDG - m_proton_PDG =
      bindingDeficit .proton - bindingDeficit .neutron
  deficit_difference_is_subrung :
    (bindingDeficit .proton - bindingDeficit .neutron)
        / (phi ^ (43 : ℕ) / 1000000 - phi ^ (42 : ℕ) / 1000000) < 0.004

theorem compositeBindingOperatorCert_holds :
    Nonempty CompositeBindingOperatorCert :=
  ⟨{ proton_reproduced := compositeMass_proton_eq_pdg
     neutron_reproduced := compositeMass_neutron_eq_pdg
     proton_deficit_pos := bindingDeficit_proton_pos
     neutron_deficit_pos := bindingDeficit_neutron_pos
     proton_deficit_band := proton_deficit_30_33MeV
     neutron_deficit_band := neutron_deficit_29_31MeV
     proton_valence_negligible := by
       simpa [valenceMass, ProtonBindingDerivation.valence_mass_sum]
         using valence_fraction_lt_1pct
     neutron_valence_negligible := neutron_valence_fraction_lt_2pct
     neutron_binding_dominates := neutron_binding_dominance
     np_split_is_deficit_difference := np_split_eq_deficit_difference
     deficit_difference_is_subrung := deficit_difference_subrung }⟩

end

end CompositeBindingOperator
end Masses
end IndisputableMonolith
