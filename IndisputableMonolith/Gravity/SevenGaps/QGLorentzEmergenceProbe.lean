import IndisputableMonolith.Foundation.SimplicialLedger.LorentzEmergence

/-!
Independent probe: does the Foundation Lorentz-emergence module's upper bound
carry the subluminality the photon dispersion paper predicts, and is it clean?
Written outside the module so nothing in it can be assumed.
-/

open IndisputableMonolith.Foundation.SimplicialLedger.LorentzEmergence

-- The bound holds at EVERY positive spacing, not only in a limit.
example (a : ℝ) (ha : 0 < a) (k : Fin 3 → ℝ) :
    dispersion a k ≤ continuum_isotropic k :=
  dispersion_upper_bound_by_isotropic a ha k

-- Restated as subluminality of the squared phase speed along one axis:
-- omega^2 <= k^2 at every spacing, which is the paper's sign claim.
example (a k : ℝ) (ha : 0 < a) : axis_dispersion a k ≤ k ^ 2 :=
  axis_dispersion_upper_bound a k ha

-- The gap to the isotropic value is nonnegative: the lattice never exceeds
-- the cone. A superluminal branch would refute this.
example (a k : ℝ) (ha : 0 < a) : 0 ≤ k ^ 2 - axis_dispersion a k :=
  (axis_dispersion_sandwich a k ha).1

#print axioms dispersion_upper_bound_by_isotropic
#print axioms axis_dispersion_upper_bound
#print axioms axis_dispersion_sandwich
#print axioms isotropic_envelope_rotation_invariant
