import Mathlib

/-!
# Heavy Quark Full-Closure Obstruction

This module records the numerical obstruction to a full heavy-quark closure
from the current non-mass dimensional bridge.

Using:

* `E_coh_SI` from the neutron-lifetime / Fermi route, approximately
  `2.4101e-16 eV`;
* RS-native `massAtAnchor` values:
  charm ≈ 4981.65, bottom ≈ 8248.93, top ≈ 89392.14;

the raw SI masses are many orders of magnitude below the PDG masses.
Therefore the current bridge plus `massAtAnchor` does **not** derive the
heavy-quark GeV masses. A further mass-sector bridge, if true, must be proved.

This is not a physics theorem; it is an audit certificate preventing the
scorecards from being misread as first-principles derivations.
-/

namespace IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction

/-! ## Evaluated raw predictions from current bridge -/

def charm_raw_eV : ℝ := 1.2006170448628038e-12
def bottom_raw_eV : ℝ := 1.988055339759384e-12
def top_raw_eV : ℝ := 2.1544198712797816e-11

def charm_PDG_eV : ℝ := 1.27e9
def bottom_PDG_eV : ℝ := 4.18e9
def top_PDG_eV : ℝ := 172.69e9

theorem charm_raw_far_below_PDG :
    charm_raw_eV < charm_PDG_eV / 1e18 := by
  unfold charm_raw_eV charm_PDG_eV
  norm_num

theorem bottom_raw_far_below_PDG :
    bottom_raw_eV < bottom_PDG_eV / 1e18 := by
  unfold bottom_raw_eV bottom_PDG_eV
  norm_num

theorem top_raw_far_below_PDG :
    top_raw_eV < top_PDG_eV / 1e18 := by
  unfold top_raw_eV top_PDG_eV
  norm_num

/-! ## Required extra φ-exponents, evaluated -/

def charm_required_phi_exponent : ℝ := 100.60116086852311
def bottom_required_phi_exponent : ℝ := 102.02875053742147
def top_required_phi_exponent : ℝ := 104.80972375767824

theorem required_exponents_not_equal :
    charm_required_phi_exponent ≠ bottom_required_phi_exponent ∧
    bottom_required_phi_exponent ≠ top_required_phi_exponent ∧
    charm_required_phi_exponent ≠ top_required_phi_exponent := by
  unfold charm_required_phi_exponent bottom_required_phi_exponent top_required_phi_exponent
  norm_num

/-- Audit conclusion: there is no single universal extra φ-exponent among the
three evaluated heavy-quark channels under the current bridge. -/
structure HeavyQuarkClosureObstructionCert where
  charm_below : charm_raw_eV < charm_PDG_eV / 1e18
  bottom_below : bottom_raw_eV < bottom_PDG_eV / 1e18
  top_below : top_raw_eV < top_PDG_eV / 1e18
  exponents_split :
    charm_required_phi_exponent ≠ bottom_required_phi_exponent ∧
    bottom_required_phi_exponent ≠ top_required_phi_exponent ∧
    charm_required_phi_exponent ≠ top_required_phi_exponent

theorem heavyQuarkClosureObstructionCert_holds :
    HeavyQuarkClosureObstructionCert :=
{ charm_below := charm_raw_far_below_PDG
  bottom_below := bottom_raw_far_below_PDG
  top_below := top_raw_far_below_PDG
  exponents_split := required_exponents_not_equal }

end IndisputableMonolith.Masses.HeavyQuarkFullClosureObstruction
