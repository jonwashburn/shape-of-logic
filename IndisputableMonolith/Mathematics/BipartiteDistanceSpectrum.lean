import Mathlib

/-!
# Bipartite Distance Spectrum

This module records the physicalized form of Erdős problem #661.

In RS terms the problem is a two-channel range-spectrum question:
two finite planar channels `P` and `Q` are coupled by Euclidean propagation
delay, and the classical distance count is the alphabet size of the
cross-coupling spectrum.

The positive Erdős #661 direction asks whether that alphabet can be
`o(n / sqrt(log n))`.  The RS physical reading suggests the opposite target:
in a single positive-definite planar carrier, true two-sector orthogonality is
unavailable, so the square-grid `n / sqrt(log n)` scale should be rigid.
-/

namespace IndisputableMonolith
namespace Mathematics
namespace BipartiteDistanceSpectrum

open Filter
open scoped Topology

noncomputable section

abbrev Point2 := EuclideanSpace ℝ (Fin 2)
abbrev Point4 := EuclideanSpace ℝ (Fin 4)

/-- The squared cross-distance alphabet between two finite planar channels. -/
noncomputable def crossDistSqSpectrum (P Q : Finset Point2) : Finset ℝ := by
  classical
  exact (P.product Q).image (fun pq => dist pq.1 pq.2 ^ 2)

/-- The unsquared distance alphabet.  Squaring is often cleaner algebraically,
but both alphabets carry the same asymptotic information away from sign issues
because distance is nonnegative. -/
noncomputable def crossDistSpectrum (P Q : Finset Point2) : Finset ℝ := by
  classical
  exact (P.product Q).image (fun pq => dist pq.1 pq.2)

/-- A two-channel range experiment: sources and detectors in the visible plane. -/
structure TwoChannelRangeExperiment where
  sources : Finset Point2
  detectors : Finset Point2

/-- The physical readout is the cross-coupling alphabet. -/
noncomputable def TwoChannelRangeExperiment.crossCouplingSpectrum
    (E : TwoChannelRangeExperiment) : Finset ℝ :=
  crossDistSpectrum E.sources E.detectors

/-- Trivial upper bound: the cross spectrum has at most one value per
source-detector pair. -/
theorem crossDistSqSpectrum_card_le_pairs (P Q : Finset Point2) :
    (crossDistSqSpectrum P Q).card ≤ P.card * Q.card := by
  classical
  unfold crossDistSqSpectrum
  calc
    ((P.product Q).image (fun pq => dist pq.1 pq.2 ^ 2)).card ≤
        (P.product Q).card := Finset.card_image_le
    _ = P.card * Q.card := by simp

/-- Positive formulation of Erdős #661: there are two `n`-point planar channels
whose cross-distance alphabet is little-o of the square-grid scale. -/
def Erdos661Positive : Prop :=
  ∃ P Q : ℕ → Finset Point2,
    (∀ᶠ n in atTop, (P n).card = n ∧ (Q n).card = n) ∧
      Tendsto
        (fun n : ℕ =>
          ((crossDistSpectrum (P n) (Q n)).card : ℝ) /
            ((n : ℝ) / Real.sqrt (Real.log n)))
        atTop
        (𝓝 0)

/-- Negative RS target: planar cross-spectrum rigidity at the grid scale. -/
def PlanarCrossSpectrumRigidity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n in atTop,
      ∀ P Q : Finset Point2,
        P.card = n →
        Q.card = n →
          c * ((n : ℝ) / Real.sqrt (Real.log n)) ≤
            ((crossDistSpectrum P Q).card : ℝ)

/-- Lenz-style collapse in a richer carrier: all cross-distances between two
finite channels in `ℝ⁴` are the same.  Erdős #661 is hard because this
orthogonal two-sector mechanism is not available in one planar carrier. -/
def FixedCrossDistanceInFourSpace (P Q : Finset Point4) : Prop :=
  ∃ r : ℝ, ∀ p ∈ P, ∀ q ∈ Q, dist p q = r

/-! ## Planar norm-fiber rigidity target -/

/-- Squared norm in the visible planar carrier. -/
noncomputable def normSq (p : Point2) : ℝ :=
  ‖p‖ ^ 2

/-- The squared-norm alphabet of a finite planar set. -/
noncomputable def normSqImage (A : Finset Point2) : Finset ℝ := by
  classical
  exact A.image normSq

/-- The cross-difference set `Q - P`. -/
noncomputable def crossDifferenceSet (P Q : Finset Point2) : Finset Point2 := by
  classical
  exact (P.product Q).image (fun pq => pq.2 - pq.1)

/-- The squared-norm alphabet of all cross-differences. -/
noncomputable def crossNormSqAlphabet (P Q : Finset Point2) : Finset ℝ :=
  normSqImage (crossDifferenceSet P Q)

/-- A rank-two lattice-like carrier in the visible plane, recorded only at the
level needed for the inverse theorem target.  The `basis` map is the proposed
Gaussian-integer coordinate chart; `integral_norm` says visible squared norm is
read from an integral positive binary quadratic form after scaling. -/
structure GaussianLikeLattice where
  basis : (Fin 2 → ℤ) → Point2
  scale : ℝ
  scale_pos : 0 < scale
  qform : (Fin 2 → ℤ) → ℤ
  qform_nonneg : ∀ z, 0 ≤ qform z
  integral_norm :
    ∀ z, normSq (basis z) = scale * (qform z : ℝ)

/-- A finite set is approximately carried by a Gaussian-like lattice if all but
`error` of its points lie in the lattice image.  This is deliberately weak:
future work can replace it by density-in-a-box, Freiman-isomorphism, or Hausdorff
distance variants without changing the physical statement. -/
def ApproxContainedInGaussianLikeLattice
    (A : Finset Point2) (Λ : GaussianLikeLattice) (error : ℕ) : Prop :=
  ∃ A₀ : Finset Point2,
    A₀ ⊆ A ∧
      A.card ≤ A₀.card + error ∧
      ∀ a ∈ A₀, ∃ z : Fin 2 → ℤ, Λ.basis z = a

/-- The inverse theorem target left by the RS physicalization:
small cross-norm alphabet at the Landau-Ramanujan scale forces the visible
points to be approximately carried by a Gaussian-integer-like lattice.

This is not asserted as proved here; it is the exact classical lemma needed to
turn the RS physical statement into a conventional proof. -/
def PlanarNormFiberRigidityTarget : Prop :=
  ∀ᶠ n in atTop,
    ∀ P Q : Finset Point2,
      P.card = n →
      Q.card = n →
      ((crossNormSqAlphabet P Q).card : ℝ) ≤
          (n : ℝ) / Real.sqrt (Real.log n) →
        ∃ Λ : GaussianLikeLattice,
          ApproxContainedInGaussianLikeLattice P Λ (n / 100) ∧
          ApproxContainedInGaussianLikeLattice Q Λ (n / 100)

end
end BipartiteDistanceSpectrum
end Mathematics
end IndisputableMonolith
