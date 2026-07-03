import IndisputableMonolith.Mathematics.BipartiteDistanceSpectrum

/-!
# Distance Shell Multiplicity

This module records the RS physicalization of Erdős problem #132.

Classically, a distance value is a shell in the set of pairwise Euclidean
distances.  Physically, it is a two-body recognition-energy shell.  Its
multiplicity is the shell occupancy.

We use ordered pairs for Lean simplicity.  For a positive distance, ordered
multiplicity is exactly twice the usual unordered multiplicity, so the classical
threshold `≤ n` becomes `≤ 2n`.
-/

namespace IndisputableMonolith
namespace Mathematics
namespace DistanceShellMultiplicity

open Filter
open scoped Topology

noncomputable section

abbrev Point2 := BipartiteDistanceSpectrum.Point2

/-- Ordered non-diagonal pair events in a finite planar set. -/
noncomputable def orderedPairEvents (A : Finset Point2) : Finset (Point2 × Point2) := by
  classical
  exact (A.product A).filter (fun pq => pq.1 ≠ pq.2)

/-- The ordered distance spectrum of a finite planar set. -/
noncomputable def orderedDistanceSpectrum (A : Finset Point2) : Finset ℝ := by
  classical
  exact (orderedPairEvents A).image (fun pq => dist pq.1 pq.2)

/-- Ordered multiplicity of one distance shell. -/
noncomputable def orderedShellMultiplicity (A : Finset Point2) (r : ℝ) : ℕ := by
  classical
  exact ((orderedPairEvents A).filter (fun pq => dist pq.1 pq.2 = r)).card

/-- A sparse shell in ordered-pair normalization.  This is the classical
condition "unordered multiplicity at most `n`" written as ordered multiplicity
at most `2n`. -/
def SparseShell (A : Finset Point2) (r : ℝ) : Prop :=
  r ∈ orderedDistanceSpectrum A ∧ orderedShellMultiplicity A r ≤ 2 * A.card

/-- Diameter shell, expressed by the maximum-distance predicate. -/
def IsDiameterShell (A : Finset Point2) (r : ℝ) : Prop :=
  r ∈ orderedDistanceSpectrum A ∧
    ∀ s ∈ orderedDistanceSpectrum A, s ≤ r

/-- The diameter value of a finite planar set is nonnegative because it is the
distance between two points in the set. -/
theorem diameter_shell_nonneg
    {A : Finset Point2} {Δ : ℝ} (hΔ : IsDiameterShell A Δ) :
    0 ≤ Δ := by
  classical
  obtain ⟨pq, _, hpq⟩ := Finset.mem_image.mp hΔ.1
  rw [← hpq]
  exact dist_nonneg

/-- The diameter value is uniquely determined by the set: it is the maximum of
the ordered distance spectrum, and two maxima of the same set are equal. -/
theorem isDiameterShell_unique
    {A : Finset Point2} {Δ₁ Δ₂ : ℝ}
    (h₁ : IsDiameterShell A Δ₁) (h₂ : IsDiameterShell A Δ₂) :
    Δ₁ = Δ₂ :=
  le_antisymm (h₂.2 _ h₁.1) (h₁.2 _ h₂.1)

/-- Every pairwise distance in `A` is bounded by the diameter, including the
case where both points coincide. -/
theorem dist_le_of_diameter_shell
    {A : Finset Point2} {Δ : ℝ} (hΔ : IsDiameterShell A Δ)
    {x y : Point2} (hx : x ∈ A) (hy : y ∈ A) :
    dist x y ≤ Δ := by
  classical
  by_cases hxy : x = y
  · subst hxy
    have h0 : dist x x = 0 := by simp
    rw [h0]
    exact diameter_shell_nonneg hΔ
  · have hd : dist x y ∈ orderedDistanceSpectrum A := by
      unfold orderedDistanceSpectrum
      refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
      unfold orderedPairEvents
      refine Finset.mem_filter.mpr ⟨?_, hxy⟩
      exact Finset.mem_product.mpr ⟨hx, hy⟩
    exact hΔ.2 _ hd


/-- Erdős #132 in ordered-pair normalization: for every sufficiently large
finite planar set there are two distinct sparse distance shells. -/
def Erdos132Ordered : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∃ r s : ℝ,
          r ≠ s ∧ SparseShell A r ∧ SparseShell A s

/-- Stronger RS target suggested by the shell-flux reading: the number of sparse
shells should diverge. -/
def SparseShellsDiverge : Prop :=
  Tendsto
    (fun n : ℕ =>
      sInf
        {k : ℝ |
          ∀ A : Finset Point2,
            A.card = n →
              k ≤ ((orderedDistanceSpectrum A).filter
                (fun r => orderedShellMultiplicity A r ≤ 2 * A.card)).card})
    atTop
    atTop

/-- Missing bridge named by the RS derivation: once the diameter shell is peeled
off, shell-flux conservation forces at least one further sparse shell. -/
def SecondSparseShellFluxBridge : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∃ r : ℝ, r ≠ Δ ∧ SparseShell A r

/-- The shell-flux bridge implies Erdős #132, because Hopf-Pannwitz supplies
the diameter shell as the first sparse shell.  We leave Hopf-Pannwitz as the
classical input in this statement surface. -/
def HopfPannwitzOrderedDiameterBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∃ Δ : ℝ, IsDiameterShell A Δ ∧ SparseShell A Δ

/-- Existence of a diameter shell for sufficiently large finite planar sets.
This is finite-order bookkeeping: the nonempty ordered distance spectrum has
a maximum.  It is separated from Hopf-Pannwitz because the latter's genuine
geometry is the sparsity bound, not maximum existence. -/
def DiameterShellExistsEventually : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∃ Δ : ℝ, IsDiameterShell A Δ

/-- Hopf-Pannwitz sparsity component: every diameter shell is sparse in the
ordered normalization.  This is the straight-line-thrackle theorem bridge. -/
def DiameterShellSparseBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ, IsDiameterShell A Δ → SparseShell A Δ

/-- Ordered diameter-edge set for a given shell value. -/
noncomputable def diameterOrderedEdges (A : Finset Point2) (Δ : ℝ) :
    Finset (Point2 × Point2) := by
  classical
  exact (orderedPairEvents A).filter (fun pq => dist pq.1 pq.2 = Δ)

/-- Ordered diameter multiplicity is the cardinality of the ordered diameter
edge set. -/
theorem orderedShellMultiplicity_eq_diameterOrderedEdges_card
    (A : Finset Point2) (Δ : ℝ) :
    orderedShellMultiplicity A Δ = (diameterOrderedEdges A Δ).card := by
  rfl

/-- An ordered diameter edge has both endpoints in `A`, distinct, and distance
exactly Δ. -/
theorem diameter_ordered_edge_data
    {A : Finset Point2} {Δ : ℝ}
    {e : Point2 × Point2} (he : e ∈ diameterOrderedEdges A Δ) :
    e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2 ∧ dist e.1 e.2 = Δ := by
  classical
  have heFilter := Finset.mem_filter.mp he
  have heDist : dist e.1 e.2 = Δ := heFilter.2
  have heEvents := Finset.mem_filter.mp heFilter.1
  have heProd := Finset.mem_product.mp heEvents.1
  exact ⟨heProd.1, heProd.2, heEvents.2, heDist⟩

/-- Convenience bundle: all four cross-distances between two ordered diameter
edges are bounded by the diameter, and both edge-distances equal Δ. -/
theorem diameter_ordered_edges_cross_distances_le
    {A : Finset Point2} {Δ : ℝ}
    (hΔ : IsDiameterShell A Δ)
    {e f : Point2 × Point2}
    (he : e ∈ diameterOrderedEdges A Δ)
    (hf : f ∈ diameterOrderedEdges A Δ) :
    dist e.1 e.2 = Δ ∧ dist f.1 f.2 = Δ ∧
    dist e.1 f.1 ≤ Δ ∧ dist e.1 f.2 ≤ Δ ∧
    dist e.2 f.1 ≤ Δ ∧ dist e.2 f.2 ≤ Δ := by
  rcases diameter_ordered_edge_data he with ⟨he1A, he2A, _, heDist⟩
  rcases diameter_ordered_edge_data hf with ⟨hf1A, hf2A, _, hfDist⟩
  refine ⟨heDist, hfDist, ?_, ?_, ?_, ?_⟩
  · exact dist_le_of_diameter_shell hΔ he1A hf1A
  · exact dist_le_of_diameter_shell hΔ he1A hf2A
  · exact dist_le_of_diameter_shell hΔ he2A hf1A
  · exact dist_le_of_diameter_shell hΔ he2A hf2A

/-- Diameter sparsity stripped to its real content: the ordered diameter shell
has at most `2n` directed events.  Membership in the spectrum comes separately
from `IsDiameterShell`. -/
def DiameterShellOrderedMultiplicityBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            orderedShellMultiplicity A Δ ≤ 2 * A.card

/-- The ordered multiplicity bound implies the sparse-shell bridge. -/
theorem diameter_shell_sparse_from_ordered_bound
    (hBound : DiameterShellOrderedMultiplicityBound) :
    DiameterShellSparseBound := by
  filter_upwards [hBound] with n hBoundN
  intro A hA Δ hΔ
  exact ⟨hΔ.1, hBoundN A hA Δ hΔ⟩

/-- Closed line segment between two visible planar states. -/
def OnClosedSegment (a b x : Point2) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = (1 - t) • a + t • b

/-- The left endpoint lies on its closed segment. -/
theorem left_endpoint_on_segment (a b : Point2) :
    OnClosedSegment a b a := by
  refine ⟨0, by norm_num, by norm_num, ?_⟩
  simp

/-- The right endpoint lies on its closed segment. -/
theorem right_endpoint_on_segment (a b : Point2) :
    OnClosedSegment a b b := by
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  simp

/-- A closed segment is symmetric in its endpoints. -/
theorem on_closed_segment_symm
    {a b x : Point2} (h : OnClosedSegment a b x) :
    OnClosedSegment b a x := by
  rcases h with ⟨t, h0, h1, hx⟩
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  rw [hx]
  module

/-- Symmetry as an iff. -/
theorem on_closed_segment_comm (a b x : Point2) :
    OnClosedSegment a b x ↔ OnClosedSegment b a x :=
  ⟨on_closed_segment_symm, on_closed_segment_symm⟩

/-- The midpoint of `[a, b]` lies on the closed segment. -/
theorem midpoint_on_closed_segment (a b : Point2) :
    OnClosedSegment a b ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
  module

/-- A closed segment is convex under affine combinations: any weighted combo of
two points on `[a, b]` is again on `[a, b]`. -/
theorem on_closed_segment_convex
    {a b x y : Point2}
    (hx : OnClosedSegment a b x) (hy : OnClosedSegment a b y)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    OnClosedSegment a b ((1 - s) • x + s • y) := by
  rcases hx with ⟨t₁, ht₁0, ht₁1, hx_eq⟩
  rcases hy with ⟨t₂, ht₂0, ht₂1, hy_eq⟩
  refine ⟨(1 - s) * t₁ + s * t₂, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [hx_eq, hy_eq]
    module

/-- The degenerate segment `[a, a]` contains only the point `a`. -/
theorem on_closed_segment_self_eq
    {a x : Point2} (hx : OnClosedSegment a a x) :
    x = a := by
  rcases hx with ⟨t, _, _, hx_eq⟩
  rw [hx_eq]
  module

/-- Triangle equality on a closed segment: any interior point `x` satisfies
`dist a x + dist x b = dist a b`. -/
theorem dist_add_on_closed_segment
    {a b x : Point2} (hx : OnClosedSegment a b x) :
    dist a x + dist x b = dist a b := by
  rcases hx with ⟨t, h0, h1, hx_eq⟩
  rw [hx_eq, dist_eq_norm, dist_eq_norm, dist_eq_norm]
  have h_left : a - ((1 - t) • a + t • b) = t • (a - b) := by module
  have h_right : ((1 - t) • a + t • b) - b = (1 - t) • (a - b) := by module
  rw [h_left, h_right, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg h0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
  ring

/-- Either endpoint distance is dominated by the segment length. -/
theorem dist_left_le_of_on_closed_segment
    {a b x : Point2} (hx : OnClosedSegment a b x) :
    dist a x ≤ dist a b := by
  have hadd := dist_add_on_closed_segment hx
  have hpos : 0 ≤ dist x b := dist_nonneg
  linarith

/-- Either endpoint distance is dominated by the segment length. -/
theorem dist_right_le_of_on_closed_segment
    {a b x : Point2} (hx : OnClosedSegment a b x) :
    dist x b ≤ dist a b := by
  have hadd := dist_add_on_closed_segment hx
  have hpos : 0 ≤ dist a x := dist_nonneg
  linarith

/-- If a point on `[a,b]` is as far from `a` as `b` is, then it is `b`. -/
theorem eq_right_of_on_closed_segment_of_dist_left_eq
    {a b x : Point2} (hx : OnClosedSegment a b x)
    (hd : dist a x = dist a b) :
    x = b := by
  have hadd := dist_add_on_closed_segment hx
  have hxb : dist x b = 0 := by linarith [hadd, hd]
  exact eq_of_dist_eq_zero hxb

/-- If a point on `[a,b]` is as far from `b` as `a` is, then it is `a`. -/
theorem eq_left_of_on_closed_segment_of_dist_right_eq
    {a b x : Point2} (hx : OnClosedSegment a b x)
    (hd : dist x b = dist a b) :
    x = a := by
  have hadd := dist_add_on_closed_segment hx
  have hax : dist a x = 0 := by linarith [hadd, hd]
  exact eq_of_dist_eq_zero (by simpa [dist_comm] using hax)

/-- `OnClosedSegment` is the same as Mathlib's `segment ℝ`, unlocking the full
convex-segment library. -/
theorem onClosedSegment_iff_mem_segment
    (a b x : Point2) :
    OnClosedSegment a b x ↔ x ∈ segment ℝ a b := by
  constructor
  · rintro ⟨t, h0, h1, hx⟩
    refine ⟨1 - t, t, by linarith, h0, by ring, ?_⟩
    rw [← hx]
  · rintro ⟨s, t, hs, ht, hst, hx⟩
    refine ⟨t, ht, ?_, ?_⟩
    · linarith
    · have hs_eq : s = 1 - t := by linarith
      rw [← hx, hs_eq]

/-- An interior point of a closed segment that is not an endpoint has strict
parameter `0 < t < 1`. -/
theorem on_closed_segment_strict
    {a b x : Point2} (hx : OnClosedSegment a b x)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = (1 - t) • a + t • b := by
  rcases hx with ⟨t, h0, h1, hx_eq⟩
  refine ⟨t, ?_, ?_, hx_eq⟩
  · by_contra h
    push_neg at h
    have ht : t = 0 := le_antisymm h h0
    apply hxa
    rw [hx_eq, ht]
    module
  · by_contra h
    push_neg at h
    have ht : t = 1 := le_antisymm h1 h
    apply hxb
    rw [hx_eq, ht]
    module

/-- Two ordered edges meet geometrically if their closed straight-line segments
intersect. -/
def OrderedEdgesMeetGeometrically
    (e f : Point2 × Point2) : Prop :=
  ∃ x : Point2, OnClosedSegment e.1 e.2 x ∧ OnClosedSegment f.1 f.2 x

/-- Two ordered edges are geometrically disjoint when their closed straight-line
segments do not intersect.  This is the correct Hopf-Pannwitz / thrackle
predicate; endpoint-disjointness alone is too strong and would wrongly exclude
crossing diameter diagonals. -/
def OrderedEdgesGeometricallyDisjoint
    (e f : Point2 × Point2) : Prop :=
  ¬ OrderedEdgesMeetGeometrically e f

/-- Geometric meeting is symmetric in the two ordered edges. -/
theorem ordered_edges_meet_symm
    {e f : Point2 × Point2} (h : OrderedEdgesMeetGeometrically e f) :
    OrderedEdgesMeetGeometrically f e := by
  rcases h with ⟨x, hex, hfx⟩
  exact ⟨x, hfx, hex⟩

/-- Symmetric form of the meeting predicate. -/
theorem ordered_edges_meet_comm (e f : Point2 × Point2) :
    OrderedEdgesMeetGeometrically e f ↔ OrderedEdgesMeetGeometrically f e :=
  ⟨ordered_edges_meet_symm, ordered_edges_meet_symm⟩

/-- Swapping the endpoints of the first edge preserves geometric meeting,
because the closed segment is symmetric in its endpoints. -/
theorem ordered_edges_meet_swap_left
    {a b : Point2} {f : Point2 × Point2}
    (h : OrderedEdgesMeetGeometrically (a, b) f) :
    OrderedEdgesMeetGeometrically (b, a) f := by
  rcases h with ⟨x, hab, hf⟩
  exact ⟨x, on_closed_segment_symm hab, hf⟩

/-- Swapping the endpoints of the second edge preserves geometric meeting. -/
theorem ordered_edges_meet_swap_right
    {e : Point2 × Point2} {c d : Point2}
    (h : OrderedEdgesMeetGeometrically e (c, d)) :
    OrderedEdgesMeetGeometrically e (d, c) := by
  rcases h with ⟨x, he, hcd⟩
  exact ⟨x, he, on_closed_segment_symm hcd⟩

/-- If the first endpoint of `f` lies on segment `e`, the edges meet at that
endpoint. -/
theorem ordered_edges_meet_of_fst_on_segment
    (a b c d : Point2)
    (hc : OnClosedSegment a b c) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) :=
  ⟨c, hc, left_endpoint_on_segment c d⟩

/-- If the second endpoint of `f` lies on segment `e`, the edges meet there. -/
theorem ordered_edges_meet_of_snd_on_segment
    (a b c d : Point2)
    (hd : OnClosedSegment a b d) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) :=
  ⟨d, hd, right_endpoint_on_segment c d⟩

/-- If the first endpoint of `e` lies on segment `f`, the edges meet there. -/
theorem ordered_edges_meet_of_fst_on_segment_symm
    (a b c d : Point2)
    (ha : OnClosedSegment c d a) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) :=
  ⟨a, left_endpoint_on_segment a b, ha⟩

/-- If the second endpoint of `e` lies on segment `f`, the edges meet there. -/
theorem ordered_edges_meet_of_snd_on_segment_symm
    (a b c d : Point2)
    (hb : OnClosedSegment c d b) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) :=
  ⟨b, right_endpoint_on_segment a b, hb⟩

/-- Two ordered edges share an endpoint. -/
def OrderedEdgesShareEndpoint
    (e f : Point2 × Point2) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2

/-- Shared endpoint implies geometric meeting of the closed segments. -/
theorem ordered_edges_meet_of_share_endpoint
    {e f : Point2 × Point2}
    (h : OrderedEdgesShareEndpoint e f) :
    OrderedEdgesMeetGeometrically e f := by
  rcases h with h11 | h12 | h21 | h22
  · refine ⟨e.1, left_endpoint_on_segment e.1 e.2, ?_⟩
    rw [← h11]
    exact left_endpoint_on_segment e.1 f.2
  · refine ⟨e.1, left_endpoint_on_segment e.1 e.2, ?_⟩
    rw [← h12]
    exact right_endpoint_on_segment f.1 e.1
  · refine ⟨e.2, right_endpoint_on_segment e.1 e.2, ?_⟩
    rw [← h21]
    exact left_endpoint_on_segment e.2 f.2
  · refine ⟨e.2, right_endpoint_on_segment e.1 e.2, ?_⟩
    rw [← h22]
    exact right_endpoint_on_segment f.1 e.2

/-- Diameter-edge graph has no two geometrically disjoint edges.  This is the
geometric observation behind Hopf-Pannwitz. -/
def NoDisjointDiameterEdges : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∀ e ∈ diameterOrderedEdges A Δ,
              ∀ f ∈ diameterOrderedEdges A Δ,
                ¬ OrderedEdgesGeometricallyDisjoint e f

/-- Local geometric lemma: any two diameter segments in the same finite planar
set meet.  This is the four-point geometric core behind
`NoDisjointDiameterEdges`. -/
def DiameterSegmentsMeetLocally : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∀ e ∈ diameterOrderedEdges A Δ,
              ∀ f ∈ diameterOrderedEdges A Δ,
                OrderedEdgesMeetGeometrically e f

/-- The remaining local geometric core after endpoint-sharing cases are
discharged: endpoint-disjoint diameter segments must meet. -/
def EndpointDisjointDiameterSegmentsMeetLocally : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∀ e ∈ diameterOrderedEdges A Δ,
              ∀ f ∈ diameterOrderedEdges A Δ,
                ¬ OrderedEdgesShareEndpoint e f →
                  OrderedEdgesMeetGeometrically e f

/-- Endpoint-disjoint local meeting plus the elementary shared-endpoint lemma
gives the full local meeting bridge. -/
theorem diameter_segments_meet_from_endpoint_disjoint_core
    (hCore : EndpointDisjointDiameterSegmentsMeetLocally) :
    DiameterSegmentsMeetLocally := by
  filter_upwards [hCore] with n hCoreN
  intro A hA Δ hΔ e he f hf
  by_cases hShare : OrderedEdgesShareEndpoint e f
  · exact ordered_edges_meet_of_share_endpoint hShare
  · exact hCoreN A hA Δ hΔ e he f hf hShare

/-- Four-point diameter crossing lemma: any two endpoint-disjoint diameter pairs
in the plane, with all six pairwise distances bounded by the diameter, have
intersecting closed segments.  This is the universal four-point geometric core
behind Hopf-Pannwitz; it does not depend on `n` or on the ambient finite set. -/
def FourPointDiameterCrossing : Prop :=
  ∀ (a b c d : Point2) (Δ : ℝ),
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    dist a b = Δ →
    dist c d = Δ →
    dist a c ≤ Δ →
    dist a d ≤ Δ →
    dist b c ≤ Δ →
    dist b d ≤ Δ →
      OrderedEdgesMeetGeometrically (a, b) (c, d)

/-- The `Δ = 0` case of `FourPointDiameterCrossing` is vacuously true: the
hypotheses force `a = c` and `c ≠ a` simultaneously. -/
theorem four_point_diameter_crossing_zero_case
    (a b c d : Point2)
    (h_ac : a ≠ c) (_h_ad : a ≠ d) (_h_bc : b ≠ c) (_h_bd : b ≠ d)
    (_hab : dist a b = (0 : ℝ))
    (_hcd : dist c d = (0 : ℝ))
    (h_ac_le : dist a c ≤ (0 : ℝ))
    (_h_ad_le : dist a d ≤ (0 : ℝ))
    (_h_bc_le : dist b c ≤ (0 : ℝ))
    (_h_bd_le : dist b d ≤ (0 : ℝ)) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) := by
  exfalso
  have hac : dist a c = 0 := le_antisymm h_ac_le dist_nonneg
  exact h_ac (eq_of_dist_eq_zero hac)

/-- Signed twice-area / orientation determinant in the visible plane. -/
noncomputable def orient2 (a b c : Point2) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-- Swapping the first two arguments negates orientation. -/
theorem orient2_swap₁₂ (a b c : Point2) :
    orient2 b a c = - orient2 a b c := by
  unfold orient2
  ring

/-- Swapping the last two arguments negates orientation. -/
theorem orient2_swap₂₃ (a b c : Point2) :
    orient2 a c b = - orient2 a b c := by
  unfold orient2
  ring

/-- Swapping the first and last arguments negates orientation. -/
theorem orient2_swap₁₃ (a b c : Point2) :
    orient2 c b a = - orient2 a b c := by
  unfold orient2
  ring

/-- Cyclic permutation preserves orientation: `orient2 a b c = orient2 b c a`. -/
theorem orient2_cyclic (a b c : Point2) :
    orient2 a b c = orient2 b c a := by
  unfold orient2
  ring

/-- Cyclic permutation preserves orientation: `orient2 a b c = orient2 c a b`. -/
theorem orient2_cyclic' (a b c : Point2) :
    orient2 a b c = orient2 c a b := by
  rw [orient2_cyclic, orient2_cyclic]

/-- Four-point Plücker orientation identity: signed areas of triangles among
four points satisfy a single linear relation. -/
theorem orient2_plucker (a b c d : Point2) :
    orient2 a b c + orient2 a c d = orient2 a b d + orient2 b c d := by
  unfold orient2
  ring

/-- Plücker identity solved for `orient2 b c d`. -/
theorem orient2_bcd_decomposition (a b c d : Point2) :
    orient2 b c d = orient2 a b c - orient2 a b d + orient2 a c d := by
  unfold orient2
  ring

/-- Plücker identity in zero-sum form: an alternating sum of the four triangle
orientations vanishes. -/
theorem orient2_alternating_sum_eq_zero (a b c d : Point2) :
    orient2 a b c - orient2 a b d + orient2 a c d - orient2 b c d = 0 := by
  unfold orient2
  ring

/-- Orientation zero is transitive through a fixed line: if `c` and `d` both lie
on the line through `a, b` (so `orient2 a b c = 0 = orient2 a b d`), and
`a ≠ b`, then `orient2 a c d = 0`. Equivalently: collinear `{a,b,c}` and
collinear `{a,b,d}` with `a ≠ b` implies `{a,c,d}` collinear. -/
theorem orient2_zero_transitive
    {a b c d : Point2} (hab : a ≠ b)
    (hc : orient2 a b c = 0) (hd : orient2 a b d = 0) :
    orient2 a c d = 0 := by
  have hne : ∃ i : Fin 2, a i ≠ b i := by
    by_contra h
    push_neg at h
    exact hab (by ext i; exact h i)
  unfold orient2 at hc hd ⊢
  set p := b 0 - a 0 with hp_def
  set q := b 1 - a 1 with hq_def
  set r := c 0 - a 0 with hr_def
  set s := c 1 - a 1 with hs_def
  set u := d 0 - a 0 with hu_def
  set v := d 1 - a 1 with hv_def
  have key_q : q * (r * v - s * u) = 0 := by linear_combination -v * hc + s * hd
  have key_p : p * (r * v - s * u) = 0 := by linear_combination -u * hc + r * hd
  rcases hne with ⟨i, hi⟩
  fin_cases i
  · have hp : p ≠ 0 := sub_ne_zero.mpr hi.symm
    have hrvsu : r * v - s * u = 0 := by
      rcases mul_eq_zero.mp key_p with h | h
      · exact absurd h hp
      · exact h
    linarith
  · have hq : q ≠ 0 := sub_ne_zero.mpr hi.symm
    have hrvsu : r * v - s * u = 0 := by
      rcases mul_eq_zero.mp key_q with h | h
      · exact absurd h hq
      · exact h
    linarith

/-- Symmetric variant of `orient2_zero_transitive`: with `c ≠ d`, both `a` and
`b` lie on the line through `c, d`. Useful for the four-point collinear
analysis. -/
theorem orient2_zero_transitive_swap
    {a b c d : Point2} (hcd : c ≠ d)
    (hca : orient2 c d a = 0) (hcb : orient2 c d b = 0) :
    orient2 c a b = 0 := orient2_zero_transitive hcd hca hcb

/-- Transfer collinearity through two distinct common points.  If `x` and `y`
are distinct points on line `ab`, and `c` lies on line `xy`, then `c` lies on
line `ab`. -/
theorem orient2_zero_of_two_points_on_line_and_point_on_join
    {a b x y c : Point2} (hxy : x ≠ y)
    (hx : orient2 a b x = 0) (hy : orient2 a b y = 0)
    (hc : orient2 x y c = 0) :
    orient2 a b c = 0 := by
  have hcoord : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
    by_contra h
    push_neg at h
    exact hxy (by ext i; fin_cases i; exact h.1; exact h.2)
  rcases hcoord with h0 | h1
  · have hdiff : (b 0 - a 0) * (y 1 - x 1) - (b 1 - a 1) * (y 0 - x 0) = 0 := by
      unfold orient2 at hx hy
      linear_combination hy - hx
    have key : (y 0 - x 0) * orient2 a b c = 0 := by
      unfold orient2 at hx hc ⊢
      linear_combination (y 0 - x 0) * hx + (b 0 - a 0) * hc + (c 0 - x 0) * hdiff
    have hyx : y 0 - x 0 ≠ 0 := sub_ne_zero.mpr h0.symm
    exact (mul_eq_zero.mp key).resolve_left hyx
  · have hdiff : (b 0 - a 0) * (y 1 - x 1) - (b 1 - a 1) * (y 0 - x 0) = 0 := by
      unfold orient2 at hx hy
      linear_combination hy - hx
    have key : (y 1 - x 1) * orient2 a b c = 0 := by
      unfold orient2 at hx hc ⊢
      linear_combination (y 1 - x 1) * hx + (c 1 - x 1) * hdiff + (b 1 - a 1) * hc
    have hyx : y 1 - x 1 ≠ 0 := sub_ne_zero.mpr h1.symm
    exact (mul_eq_zero.mp key).resolve_left hyx

/-- Orientation vanishes when the third point is the first endpoint. -/
theorem orient2_left_self (a b : Point2) :
    orient2 a b a = 0 := by
  unfold orient2
  ring

/-- Orientation vanishes when the third point is the second endpoint. -/
theorem orient2_right_self (a b : Point2) :
    orient2 a b b = 0 := by
  unfold orient2
  ring

/-- Any point on a closed segment is collinear with its endpoints in the
orientation determinant. -/
theorem orient2_eq_zero_of_on_closed_segment
    {a b x : Point2} (hx : OnClosedSegment a b x) :
    orient2 a b x = 0 := by
  rcases hx with ⟨t, _, _, hx_eq⟩
  rw [hx_eq]
  unfold orient2
  simp
  ring_nf

/-- Orientation is affine in the third argument along a segment. -/
theorem orient2_affine_third
    (a b c d : Point2) (t : ℝ) :
    orient2 a b ((1 - t) • c + t • d) =
      (1 - t) * orient2 a b c + t * orient2 a b d := by
  unfold orient2
  simp
  ring_nf

/-- If `x` lies on `[c,d]`, then its orientation relative to line `ab` is a
convex affine combination of the endpoint orientations. -/
theorem orient2_of_on_closed_segment
    {a b c d x : Point2} (hx : OnClosedSegment c d x) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      orient2 a b x = (1 - t) * orient2 a b c + t * orient2 a b d := by
  rcases hx with ⟨t, h0, h1, hx_eq⟩
  refine ⟨t, h0, h1, ?_⟩
  rw [hx_eq]
  exact orient2_affine_third a b c d t

/-- Parametrization on a line: if `orient2 a b c = 0` with `a ≠ b`, then there
exists a scalar `t` such that `c i - a i = t * (b i - a i)` for both
coordinates `i : Fin 2`.  This is the central planar-collinearity unpack. -/
theorem exists_scalar_of_orient2_zero
    {a b c : Point2} (hab : a ≠ b) (h : orient2 a b c = 0) :
    ∃ t : ℝ, ∀ i : Fin 2, c i - a i = t * (b i - a i) := by
  have hcoord : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra hh
    push_neg at hh
    exact hab (by ext i; fin_cases i; exact hh.1; exact hh.2)
  unfold orient2 at h
  rcases hcoord with hi0 | hi1
  · have hp : b 0 - a 0 ≠ 0 := sub_ne_zero.mpr hi0.symm
    refine ⟨(c 0 - a 0) / (b 0 - a 0), fun j => ?_⟩
    fin_cases j
    · show c 0 - a 0 = (c 0 - a 0) / (b 0 - a 0) * (b 0 - a 0)
      field_simp
    · show c 1 - a 1 = (c 0 - a 0) / (b 0 - a 0) * (b 1 - a 1)
      field_simp
      linarith
  · have hq : b 1 - a 1 ≠ 0 := sub_ne_zero.mpr hi1.symm
    refine ⟨(c 1 - a 1) / (b 1 - a 1), fun j => ?_⟩
    fin_cases j
    · show c 0 - a 0 = (c 1 - a 1) / (b 1 - a 1) * (b 0 - a 0)
      field_simp
      linarith
    · show c 1 - a 1 = (c 1 - a 1) / (b 1 - a 1) * (b 1 - a 1)
      field_simp

/-- Generalised distance lemma: if `v i - u i = t * (b i - a i)` for both
coordinates, then `dist u v = |t| * dist a b`.  This packages the
collinearity-with-base-segment squared-distance computation in one form
that handles all four orderings (a, c), (a, d), (b, c), (b, d), (c, d). -/
theorem dist_from_diff_eq_smul
    {a b u v : Point2} {t : ℝ}
    (h : ∀ i : Fin 2, v i - u i = t * (b i - a i)) :
    dist u v = |t| * dist a b := by
  have h0 : u 0 - v 0 = -t * (b 0 - a 0) := by linarith [h 0]
  have h1 : u 1 - v 1 = -t * (b 1 - a 1) := by linarith [h 1]
  have hsq : (dist u v) ^ 2 = t^2 * (dist a b) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_two, Real.dist_eq]
    have e0 : (u 0 - v 0)^2 = t^2 * (b 0 - a 0)^2 := by rw [h0]; ring
    have e1 : (u 1 - v 1)^2 = t^2 * (b 1 - a 1)^2 := by rw [h1]; ring
    have e0' : (a 0 - b 0)^2 = (b 0 - a 0)^2 := by ring
    have e1' : (a 1 - b 1)^2 = (b 1 - a 1)^2 := by ring
    linarith
  have huv_nn : 0 ≤ dist u v := dist_nonneg
  have hab_nn : 0 ≤ dist a b := dist_nonneg
  have hrhs : 0 ≤ |t| * dist a b := mul_nonneg (abs_nonneg _) hab_nn
  have hsq2 : (dist u v) ^ 2 = (|t| * dist a b) ^ 2 := by
    rw [hsq, mul_pow, sq_abs]
  have h_abs : |dist u v| = |(|t| * dist a b)| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq2
  rw [abs_of_nonneg huv_nn, abs_of_nonneg hrhs] at h_abs
  exact h_abs

/-- A real affine segment between a nonpositive and a nonnegative value crosses
zero. -/
theorem affine_zero_of_nonpos_nonneg
    {u v : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (1 - t) * u + t * v = 0 := by
  by_cases hsum : u = v
  · have hu0 : u = 0 := by linarith
    have hv0 : v = 0 := by linarith
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    rw [hu0, hv0]
    ring
  · let t := (-u) / (v - u)
    have hden_pos : 0 < v - u := by
      have : u < v := lt_of_le_of_ne (by linarith) hsum
      linarith
    refine ⟨t, ?_, ?_, ?_⟩
    · dsimp [t]
      exact div_nonneg (by linarith) (le_of_lt hden_pos)
    · dsimp [t]
      rw [div_le_one hden_pos]
      linarith
    · dsimp [t]
      field_simp [ne_of_gt hden_pos]
      ring

/-- If endpoints of segment `[c,d]` have opposite orientation signs with
respect to line `ab`, then some point of `[c,d]` lies on line `ab`
(`orient2 = 0`). -/
theorem exists_orient2_zero_on_segment_of_nonpos_nonneg
    {a b c d : Point2}
    (hc : orient2 a b c ≤ 0) (hd : 0 ≤ orient2 a b d) :
    ∃ x : Point2, OnClosedSegment c d x ∧ orient2 a b x = 0 := by
  rcases affine_zero_of_nonpos_nonneg (u := orient2 a b c)
      (v := orient2 a b d) hc hd with ⟨t, ht0, ht1, htzero⟩
  let x : Point2 := (1 - t) • c + t • d
  refine ⟨x, ⟨t, ht0, ht1, rfl⟩, ?_⟩
  rw [orient2_affine_third]
  exact htzero

/-- Symmetric version of the previous crossing lemma. -/
theorem exists_orient2_zero_on_segment_of_nonneg_nonpos
    {a b c d : Point2}
    (hc : 0 ≤ orient2 a b c) (hd : orient2 a b d ≤ 0) :
    ∃ x : Point2, OnClosedSegment c d x ∧ orient2 a b x = 0 := by
  rcases exists_orient2_zero_on_segment_of_nonpos_nonneg
      (a := a) (b := b) (c := d) (d := c) hd hc with ⟨x, hx, hz⟩
  exact ⟨x, on_closed_segment_symm hx, hz⟩

/-- Positive product over reals means the two factors have the same strict
sign. -/
theorem same_strict_sign_of_pos_mul
    {x y : ℝ} (h : 0 < x * y) :
    (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · right
    constructor
    · exact hx
    · by_contra hy_nonneg
      push_neg at hy_nonneg
      have hxy : x * y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hy_nonneg
      linarith
  · subst hx
    simp at h
  · left
    constructor
    · exact hx
    · by_contra hy_nonpos
      push_neg at hy_nonpos
      have hxy : x * y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx) hy_nonpos
      linarith

/-- A convex affine combination of two same-strict-sign real numbers is
nonzero.  This is the scalar sign fact used in orientation crossing arguments. -/
theorem convex_combo_ne_zero_of_same_strict_sign
    {u v t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : (0 < u ∧ 0 < v) ∨ (u < 0 ∧ v < 0)) :
    (1 - t) * u + t * v ≠ 0 := by
  rcases h with hpos | hneg
  · have hnonneg1 : 0 ≤ 1 - t := by linarith
    have hterm1 : 0 ≤ (1 - t) * u := mul_nonneg hnonneg1 (le_of_lt hpos.1)
    have hterm2 : 0 ≤ t * v := mul_nonneg ht0 (le_of_lt hpos.2)
    have hsum_pos_cases : 0 < (1 - t) * u ∨ 0 < t * v := by
      by_cases ht_zero : t = 0
      · left
        have : 1 - t = 1 := by linarith
        rw [this]
        simpa using hpos.1
      · right
        have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
        exact mul_pos ht_pos hpos.2
    rcases hsum_pos_cases with hp | hp
    · exact ne_of_gt (add_pos_of_pos_of_nonneg hp hterm2)
    · exact ne_of_gt (add_pos_of_nonneg_of_pos hterm1 hp)
  · have hpos' : 0 < -u ∧ 0 < -v := by
      constructor <;> linarith
    have hnonzero_pos : (1 - t) * (-u) + t * (-v) ≠ 0 := by
      have hnonneg1 : 0 ≤ 1 - t := by linarith
      have hterm1 : 0 ≤ (1 - t) * (-u) := mul_nonneg hnonneg1 (le_of_lt hpos'.1)
      have hterm2 : 0 ≤ t * (-v) := mul_nonneg ht0 (le_of_lt hpos'.2)
      have hsum_pos_cases : 0 < (1 - t) * (-u) ∨ 0 < t * (-v) := by
        by_cases ht_zero : t = 0
        · left
          have : 1 - t = 1 := by linarith
          rw [this]
          simpa using hpos'.1
        · right
          have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
          exact mul_pos ht_pos hpos'.2
      rcases hsum_pos_cases with hp | hp
      · exact ne_of_gt (add_pos_of_pos_of_nonneg hp hterm2)
      · exact ne_of_gt (add_pos_of_nonneg_of_pos hterm1 hp)
    intro hzero
    apply hnonzero_pos
    nlinarith

/-- If two points are on the same strict side of a line, the segment joining
them is disjoint from the segment spanning the line.  This is the core
separation lemma for all thrackle and matching arguments. -/
theorem same_side_segments_disjoint
    {a b c d : Point2}
    (h_same : 0 < orient2 a b c * orient2 a b d) :
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d) := by
  intro ⟨p, hp_ab, hp_cd⟩
  have h_zero : orient2 a b p = 0 :=
    orient2_eq_zero_of_on_closed_segment hp_ab
  rcases hp_cd with ⟨t, ht0, ht1, hp_eq⟩
  have h_aff : orient2 a b p = (1 - t) * orient2 a b c + t * orient2 a b d := by
    rw [hp_eq]; exact orient2_affine_third a b c d t
  rw [h_zero] at h_aff
  exact absurd h_aff.symm
    (convex_combo_ne_zero_of_same_strict_sign ht0 ht1
      (same_strict_sign_of_pos_mul h_same))

/-- A proper separating orientation certificate for two endpoint-disjoint
segments: each segment's endpoints lie strictly on one side of the line through
the other segment.  This is the standard orientation witness for two disjoint
non-collinear closed segments. -/
def ProperSegmentSeparation (a b c d : Point2) : Prop :=
  0 < orient2 a b c * orient2 a b d ∧
    0 < orient2 c d a * orient2 c d b

/-- Unpack proper separation into same-side alternatives for both supporting
lines. -/
theorem proper_segment_separation_signs
    {a b c d : Point2}
    (h : ProperSegmentSeparation a b c d) :
    ((0 < orient2 a b c ∧ 0 < orient2 a b d) ∨
      (orient2 a b c < 0 ∧ orient2 a b d < 0)) ∧
    ((0 < orient2 c d a ∧ 0 < orient2 c d b) ∨
      (orient2 c d a < 0 ∧ orient2 c d b < 0)) :=
  ⟨same_strict_sign_of_pos_mul h.1, same_strict_sign_of_pos_mul h.2⟩

/-- A proper separation certificate really implies geometric disjointness:
if the segments met, a point of `[c,d]` would also lie on line `ab`, forcing an
affine combination of two same-strict-sign orientation values to be zero. -/
theorem proper_segment_separation_geometrically_disjoint
    {a b c d : Point2}
    (h : ProperSegmentSeparation a b c d) :
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d) := by
  intro hmeet
  rcases hmeet with ⟨x, hxab, hxcd⟩
  have hx_zero : orient2 a b x = 0 := orient2_eq_zero_of_on_closed_segment hxab
  rcases orient2_of_on_closed_segment (a := a) (b := b) hxcd with
    ⟨t, ht0, ht1, hx_affine⟩
  have hsigns := (proper_segment_separation_signs h).1
  have hne :=
    convex_combo_ne_zero_of_same_strict_sign
      (u := orient2 a b c) (v := orient2 a b d) (t := t) ht0 ht1 hsigns
  exact hne (by rw [← hx_affine, hx_zero])

/-- Collinear disjoint-segment separation certificate.  The four points lie on
the same two supporting lines and the closed segments do not meet.  This is kept
separate from the strict orientation case because the products above vanish in
the collinear case. -/
def CollinearSegmentSeparation (a b c d : Point2) : Prop :=
  orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d)

/-- Abstract classical geometry bridge: if two endpoint-disjoint closed
segments do not meet, then either a proper orientation separation or a collinear
separation certificate exists.  This is the standard planar segment-separation
case split. -/
def DisjointSegmentsHaveSeparation : Prop :=
  ∀ a b c d : Point2,
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      OrderedEdgesGeometricallyDisjoint (a, b) (c, d) →
        ProperSegmentSeparation a b c d ∨ CollinearSegmentSeparation a b c d

/-- **Hopf-Pannwitz strict lens-diameter inequality** (coordinate form).
For two points `(cx, cy)` and `(dx, dy)` in the closed lens
`D((0,0), Δ) ∩ D((Δ,0), Δ)` (i.e., both visible coordinates satisfy the four
disk constraints), with `cy > 0` and `dy > 0` strict (i.e., both on the strict
upper side), the squared distance is strictly less than `Δ²`. Equivalently:
the vesica piscis has diameter `Δ` with strict inequality on the open
half-lens.

This is the central classical input for the four-point Hopf-Pannwitz lemma in
its proper-separation case. The proof is a polynomial Positivstellensatz
certificate using two orientation-determinant squares as nonnegativity hints. -/
theorem hopf_pannwitz_strict_lens_coord
    (Δ cx cy dx dy : ℝ)
    (hΔ : 0 < Δ)
    (hi : cx*cx + cy*cy ≤ Δ*Δ)
    (hii : (cx - Δ)*(cx - Δ) + cy*cy ≤ Δ*Δ)
    (hiii : dx*dx + dy*dy ≤ Δ*Δ)
    (hiv : (dx - Δ)*(dx - Δ) + dy*dy ≤ Δ*Δ)
    (hcy : 0 < cy)
    (hdy : 0 < dy) :
    (cx - dx)*(cx - dx) + (cy - dy)*(cy - dy) < Δ*Δ := by
  have hcx_pos : 0 < cx := by nlinarith [mul_pos hcy hcy]
  have hdx_pos : 0 < dx := by nlinarith [mul_pos hdy hdy]
  have hcx_lt : cx < Δ := by nlinarith [mul_pos hcy hcy]
  have hdx_lt : dx < Δ := by nlinarith [mul_pos hdy hdy]
  nlinarith [hi, hii, hiii, hiv, hcy, hdy, hcx_pos, hdx_pos, hcx_lt, hdx_lt,
             mul_pos hcy hdy, mul_self_nonneg (cy*(Δ - dx) - dy*(Δ - cx)),
             mul_self_nonneg (cy*dx - dy*cx),
             mul_pos hΔ hcy, mul_pos hΔ hdy,
             mul_pos (sub_pos.mpr hcx_lt) hdy,
             mul_pos hcy (sub_pos.mpr hdx_lt),
             mul_pos hcx_pos hdy, mul_pos hcy hdx_pos]

/-- Symmetric lens inequality: works for `cy < 0` and `dy < 0` too (the lower
half-lens), obtained by reflecting `y → -y`. -/
theorem hopf_pannwitz_strict_lens_coord_neg
    (Δ cx cy dx dy : ℝ)
    (hΔ : 0 < Δ)
    (hi : cx*cx + cy*cy ≤ Δ*Δ)
    (hii : (cx - Δ)*(cx - Δ) + cy*cy ≤ Δ*Δ)
    (hiii : dx*dx + dy*dy ≤ Δ*Δ)
    (hiv : (dx - Δ)*(dx - Δ) + dy*dy ≤ Δ*Δ)
    (hcy : cy < 0)
    (hdy : dy < 0) :
    (cx - dx)*(cx - dx) + (cy - dy)*(cy - dy) < Δ*Δ := by
  have hcy' : 0 < -cy := neg_pos.mpr hcy
  have hdy' : 0 < -dy := neg_pos.mpr hdy
  have hi' : cx*cx + (-cy)*(-cy) ≤ Δ*Δ := by nlinarith [hi]
  have hii' : (cx - Δ)*(cx - Δ) + (-cy)*(-cy) ≤ Δ*Δ := by nlinarith [hii]
  have hiii' : dx*dx + (-dy)*(-dy) ≤ Δ*Δ := by nlinarith [hiii]
  have hiv' : (dx - Δ)*(dx - Δ) + (-dy)*(-dy) ≤ Δ*Δ := by nlinarith [hiv]
  have := hopf_pannwitz_strict_lens_coord Δ cx (-cy) dx (-dy) hΔ hi' hii' hiii' hiv' hcy' hdy'
  nlinarith [this]

/-- **Lagrange's identity** in `ℝ²`: `(u·v)² + (u × v)² = |u|² |v|²`. -/
theorem lagrange_identity_2d (a b c : Point2) :
    ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1))^2 +
    ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0))^2 =
    ((c 0 - a 0)^2 + (c 1 - a 1)^2) * ((b 0 - a 0)^2 + (b 1 - a 1)^2) := by
  ring

/-- **Polarized Lagrange identity** in `ℝ²`. -/
theorem lagrange_identity_polarized_2d (a b c d : Point2) :
    ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) *
      ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1)) +
    ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) *
      ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0)) =
    ((c 0 - a 0)*(d 0 - a 0) + (c 1 - a 1)*(d 1 - a 1)) *
      ((b 0 - a 0)^2 + (b 1 - a 1)^2) := by
  ring

/-- Squared Euclidean distance unfolded for `Point2 = EuclideanSpace ℝ (Fin 2)`. -/
theorem dist_sq_unfold (a b : Point2) :
    (dist a b)^2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  have h := EuclideanSpace.dist_sq_eq a b
  simp [Fin.sum_univ_two, Real.dist_eq, pow_two] at h
  linarith [h, sq_abs (a 0 - b 0), sq_abs (a 1 - b 1)]

/-- Abstract RS/classical bridge: proper separated diameter pairs cannot satisfy
all four cross-distance bounds.  This is the positive-Δ orientation-sign core
of the four-point Hopf-Pannwitz geometry.  This bridge is now a *theorem*
(see `properSeparatedDiameterContradiction` below), so any use of
`ProperSeparatedDiameterContradiction` as a hypothesis can be discharged
unconditionally. -/
def ProperSeparatedDiameterContradiction : Prop :=
  ∀ (a b c d : Point2) (Δ : ℝ),
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    dist a b = Δ →
    dist c d = Δ →
    dist a c ≤ Δ →
    dist a d ≤ Δ →
    dist b c ≤ Δ →
    dist b d ≤ Δ →
    ProperSegmentSeparation a b c d →
      False

set_option maxHeartbeats 6400000 in
/-- **Theorem.** The proper separated diameter contradiction.  Two diameter
segments `[a,b]` and `[c,d]` with all cross-distances bounded by the diameter
cannot have both `c, d` on the strict same side of line `ab`.  Proof: place
`a` and `b` in coordinates, rotate so `(b-a)/|b-a|` is the first basis vector;
then `c, d` translate to lens-coordinate values `(αc, βc), (αd, βd)` with
`βc · Δ = orient2(a,b,c)` and `αc · Δ = ⟨c-a, b-a⟩`. Lagrange's identity
gives `αc² + βc² = (dist a c)²` and similar for the other distances. Proper
separation forces `βc · βd > 0` strict. Then `hopf_pannwitz_strict_lens_coord`
(or its negative variant) gives `(αc - αd)² + (βc - βd)² < Δ²`, but the
polarized Lagrange identity gives `(αc - αd)² + (βc - βd)² = (dist c d)² = Δ²`.
Contradiction. -/
theorem properSeparatedDiameterContradiction :
    ProperSeparatedDiameterContradiction := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hProper
  by_cases hΔ : Δ = 0
  · subst hΔ
    have h : dist a c = 0 := le_antisymm hac dist_nonneg
    exact h_ac (eq_of_dist_eq_zero h)
  have hΔ_nn : 0 ≤ Δ := hab ▸ dist_nonneg
  have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nn (Ne.symm hΔ)
  have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
  -- Δ² = P² + Q² where P = b 0 - a 0, Q = b 1 - a 1.
  have hab_sq : Δ*Δ = (b 0 - a 0)^2 + (b 1 - a 1)^2 := by
    have h := dist_sq_unfold a b
    rw [hab] at h
    nlinarith [h]
  -- Squared distances unfolded.
  have hac_sq_le : (c 0 - a 0)^2 + (c 1 - a 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold a c
    have hac_nn : 0 ≤ dist a c := dist_nonneg
    have : (dist a c)^2 ≤ Δ^2 := by nlinarith [hac_nn, hac]
    nlinarith [h, this]
  have had_sq_le : (d 0 - a 0)^2 + (d 1 - a 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold a d
    have hd_nn : 0 ≤ dist a d := dist_nonneg
    have : (dist a d)^2 ≤ Δ^2 := by nlinarith [hd_nn, had]
    nlinarith [h, this]
  have hbc_sq_le : (b 0 - c 0)^2 + (b 1 - c 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold b c
    have hd_nn : 0 ≤ dist b c := dist_nonneg
    have : (dist b c)^2 ≤ Δ^2 := by nlinarith [hd_nn, hbc]
    nlinarith [h, this]
  have hbd_sq_le : (b 0 - d 0)^2 + (b 1 - d 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold b d
    have hd_nn : 0 ≤ dist b d := dist_nonneg
    have : (dist b d)^2 ≤ Δ^2 := by nlinarith [hd_nn, hbd]
    nlinarith [h, this]
  have hcd_sq_eq : (c 0 - d 0)^2 + (c 1 - d 1)^2 = Δ*Δ := by
    have h := dist_sq_unfold c d
    rw [hcd] at h
    nlinarith [h]
  -- Un-divided HP coords:  Ac, Bc, Ad, Bd.
  -- Ac := (c-a)·(b-a) = (c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)
  -- Bc := (b-a) × (c-a) = (b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)
  -- αc = Ac/Δ, βc = Bc/Δ. Lens constraints become Ac² + Bc² ≤ Δ⁴, etc.
  -- Lagrange:  Ac² + Bc² = ((c-a)² coords)·(P² + Q²) = (dist a c)² · Δ²
  have hLag_c : ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1))^2 +
                ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0))^2 =
                ((c 0 - a 0)^2 + (c 1 - a 1)^2) * ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_2d a b c
  have hLag_d : ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1))^2 +
                ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0))^2 =
                ((d 0 - a 0)^2 + (d 1 - a 1)^2) * ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_2d a b d
  have hLag_pol : ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) *
                    ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1)) +
                  ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) *
                    ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0)) =
                  ((c 0 - a 0)*(d 0 - a 0) + (c 1 - a 1)*(d 1 - a 1)) *
                    ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_polarized_2d a b c d
  -- Set αc = Ac/Δ, βc = Bc/Δ.
  set αc := ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) / Δ with hαc_def
  set βc := ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) / Δ with hβc_def
  set αd := ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1)) / Δ with hαd_def
  set βd := ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0)) / Δ with hβd_def
  -- Lens constraints in (α, β) form: αc² + βc² ≤ Δ²  (= (dist a c)² ≤ Δ²).
  have h_αcβc_eq_ac : αc*αc + βc*βc = (c 0 - a 0)^2 + (c 1 - a 1)^2 := by
    rw [hαc_def, hβc_def]
    have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
    field_simp
    nlinarith [hLag_c, hab_sq]
  have h_αdβd_eq_ad : αd*αd + βd*βd = (d 0 - a 0)^2 + (d 1 - a 1)^2 := by
    rw [hαd_def, hβd_def]
    have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
    field_simp
    nlinarith [hLag_d, hab_sq]
  -- (αc - Δ)² + βc² = (dist b c)².
  -- |c - b|² = |c - a|² - 2(c - a)·(b - a) + |b - a|² = (αc² + βc²) - 2αc·Δ + Δ² = (αc - Δ)² + βc².
  have h_αcβc_eq_bc : (αc - Δ)*(αc - Δ) + βc*βc = (b 0 - c 0)^2 + (b 1 - c 1)^2 := by
    have e1 : αc * Δ = (c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1) := by
      rw [hαc_def]; field_simp
    have e2 : (αc - Δ)*(αc - Δ) + βc*βc = (αc*αc + βc*βc) - 2*(αc*Δ) + Δ*Δ := by ring
    rw [e2, h_αcβc_eq_ac, e1, hab_sq]
    ring
  have h_αdβd_eq_bd : (αd - Δ)*(αd - Δ) + βd*βd = (b 0 - d 0)^2 + (b 1 - d 1)^2 := by
    have e1 : αd * Δ = (d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1) := by
      rw [hαd_def]; field_simp
    have e2 : (αd - Δ)*(αd - Δ) + βd*βd = (αd*αd + βd*βd) - 2*(αd*Δ) + Δ*Δ := by ring
    rw [e2, h_αdβd_eq_ad, e1, hab_sq]
    ring
  -- (αc - αd)² + (βc - βd)² = (dist c d)².
  -- Expansion: = (αc² + βc²) - 2(αc·αd + βc·βd) + (αd² + βd²)
  --           = (|c-a|² + |d-a|²) - 2((c-a)·(d-a)) = |c - d|².
  have h_cd_eq : (αc - αd)*(αc - αd) + (βc - βd)*(βc - βd) = (c 0 - d 0)^2 + (c 1 - d 1)^2 := by
    have e1 : αc * αd + βc * βd = (c 0 - a 0)*(d 0 - a 0) + (c 1 - a 1)*(d 1 - a 1) := by
      have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
      have h1 : αc * αd = (((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) *
                          ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1))) / (Δ*Δ) := by
        rw [hαc_def, hαd_def]; field_simp
      have h2 : βc * βd = (((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) *
                          ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0))) / (Δ*Δ) := by
        rw [hβc_def, hβd_def]; field_simp
      rw [h1, h2, ← add_div]
      rw [hLag_pol, ← hab_sq]
      field_simp
    have e2 : (αc - αd)*(αc - αd) + (βc - βd)*(βc - βd) =
              (αc*αc + βc*βc) + (αd*αd + βd*βd) - 2*(αc*αd + βc*βd) := by ring
    rw [e2, h_αcβc_eq_ac, h_αdβd_eq_ad, e1]
    ring
  -- Translate orient2 sign: orient2 a b c = βc · Δ (with our sign convention).
  have hβc_orient : βc * Δ = orient2 a b c := by
    rw [hβc_def]
    field_simp
    unfold orient2
    ring
  have hβd_orient : βd * Δ = orient2 a b d := by
    rw [hβd_def]
    field_simp
    unfold orient2
    ring
  have hβ_prod : 0 < βc * βd := by
    have h := hProper.1
    have : 0 < (βc * Δ) * (βd * Δ) := by
      rw [hβc_orient, hβd_orient]; exact h
    have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
    nlinarith [this, hΔΔ_pos]
  -- Convert squared lens constraints to αc, βc form (≤ Δ*Δ form):
  have hi_lens : αc*αc + βc*βc ≤ Δ*Δ := by rw [h_αcβc_eq_ac]; exact hac_sq_le
  have hii_lens : (αc - Δ)*(αc - Δ) + βc*βc ≤ Δ*Δ := by rw [h_αcβc_eq_bc]; exact hbc_sq_le
  have hiii_lens : αd*αd + βd*βd ≤ Δ*Δ := by rw [h_αdβd_eq_ad]; exact had_sq_le
  have hiv_lens : (αd - Δ)*(αd - Δ) + βd*βd ≤ Δ*Δ := by rw [h_αdβd_eq_bd]; exact hbd_sq_le
  -- Case split on sign of βc.
  rcases lt_trichotomy βc 0 with hβc | hβc | hβc
  · -- βc < 0, βd < 0 (from positive product).
    have hβd : βd < 0 := by
      by_contra h
      push_neg at h
      have hβd_nn := h
      rcases lt_or_eq_of_le hβd_nn with hβd_pos | hβd_zero
      · have : βc * βd < 0 := mul_neg_of_neg_of_pos hβc hβd_pos
        linarith [hβ_prod, this]
      · rw [← hβd_zero] at hβ_prod; linarith
    have hp := hopf_pannwitz_strict_lens_coord_neg Δ αc βc αd βd hΔ_pos
      hi_lens hii_lens hiii_lens hiv_lens hβc hβd
    -- hp : (αc - αd)*(αc - αd) + (βc - βd)*(βc - βd) < Δ*Δ
    rw [h_cd_eq] at hp
    linarith [hp, hcd_sq_eq]
  · -- βc = 0 contradicts hβ_prod.
    rw [hβc] at hβ_prod; linarith [hβ_prod]
  · -- βc > 0, βd > 0.
    have hβd : 0 < βd := by
      by_contra h
      push_neg at h
      have hβd_le := h
      rcases lt_or_eq_of_le hβd_le with hβd_neg | hβd_zero
      · have : βc * βd < 0 := mul_neg_of_pos_of_neg hβc hβd_neg
        linarith [hβ_prod, this]
      · rw [hβd_zero] at hβ_prod; linarith
    have hp := hopf_pannwitz_strict_lens_coord Δ αc βc αd βd hΔ_pos
      hi_lens hii_lens hiii_lens hiv_lens hβc hβd
    rw [h_cd_eq] at hp
    linarith [hp, hcd_sq_eq]

/-- Abstract bridge for the collinear separated case: two disjoint collinear
diameter-length segments force one cross-distance to exceed the diameter.
This bridge is now a *theorem* (see `collinearSeparatedDiameterContradiction`
below), so any use of `CollinearSeparatedDiameterContradiction` as a hypothesis
can be discharged unconditionally. -/
def CollinearSeparatedDiameterContradiction : Prop :=
  ∀ (a b c d : Point2) (Δ : ℝ),
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    dist a b = Δ →
    dist c d = Δ →
    dist a c ≤ Δ →
    dist a d ≤ Δ →
    dist b c ≤ Δ →
    dist b d ≤ Δ →
    CollinearSegmentSeparation a b c d →
      False

/-- Collinear diameter contradiction without the unused geometric-disjointness
field.  Four collinear endpoints with equal diameter-length opposite pairs and
all four cross distances bounded by that diameter cannot be endpoint-disjoint. -/
def CollinearDiameterEndpointContradiction : Prop :=
  ∀ (a b c d : Point2) (Δ : ℝ),
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    dist a b = Δ →
    dist c d = Δ →
    dist a c ≤ Δ →
    dist a d ≤ Δ →
    dist b c ≤ Δ →
    dist b d ≤ Δ →
    orient2 a b c = 0 →
    orient2 a b d = 0 →
      False

/-- **Theorem.** Four collinear points with `dist a b = dist c d = Δ` and all
four cross distances `≤ Δ` cannot have `a ≠ c, a ≠ d, b ≠ c, b ≠ d`.  The
geometric-disjointness data in `CollinearSegmentSeparation` is not used here:
the four-point coordinate parametrization on the common line gives a
contradiction directly from `|s - t| = 1` with `t, s ∈ [0,1]` forcing
`{t,s} = {0,1}` and hence `c = a` or `c = b`. -/
theorem collinearDiameterEndpointContradiction :
    CollinearDiameterEndpointContradiction := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd h_abc h_abd
  by_cases hΔ : Δ = 0
  · subst hΔ
    have h_eq0 : dist a c = 0 := le_antisymm hac dist_nonneg
    exact h_ac (eq_of_dist_eq_zero h_eq0)
  have hΔ_nn : 0 ≤ Δ := hab ▸ dist_nonneg
  have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nn (Ne.symm hΔ)
  have h_ab : a ≠ b := by
    intro he
    rw [he, dist_self] at hab
    exact hΔ hab.symm
  obtain ⟨t, ht⟩ := exists_scalar_of_orient2_zero h_ab h_abc
  obtain ⟨s, hs⟩ := exists_scalar_of_orient2_zero h_ab h_abd
  have hac_eq : dist a c = |t| * Δ := by rw [dist_from_diff_eq_smul ht, hab]
  have had_eq : dist a d = |s| * Δ := by rw [dist_from_diff_eq_smul hs, hab]
  have hbc_param : ∀ i : Fin 2, c i - b i = (t - 1) * (b i - a i) := by
    intro i; have := ht i; linarith
  have hbc_eq : dist b c = |t - 1| * Δ := by
    rw [dist_from_diff_eq_smul hbc_param, hab]
  have hbd_param : ∀ i : Fin 2, d i - b i = (s - 1) * (b i - a i) := by
    intro i; have := hs i; linarith
  have hbd_eq : dist b d = |s - 1| * Δ := by
    rw [dist_from_diff_eq_smul hbd_param, hab]
  have hcd_param : ∀ i : Fin 2, d i - c i = (s - t) * (b i - a i) := by
    intro i
    have h1 := ht i
    have h2 := hs i
    linarith
  have hcd_eq : dist c d = |s - t| * Δ := by
    rw [dist_from_diff_eq_smul hcd_param, hab]
  have habst : |t| ≤ 1 := by
    have h1 : |t| * Δ ≤ 1 * Δ := by
      rw [one_mul]; linarith [hac_eq ▸ hac]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have habs1mt : |t - 1| ≤ 1 := by
    have h1 : |t - 1| * Δ ≤ 1 * Δ := by
      rw [one_mul]; linarith [hbc_eq ▸ hbc]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have habss : |s| ≤ 1 := by
    have h1 : |s| * Δ ≤ 1 * Δ := by
      rw [one_mul]; linarith [had_eq ▸ had]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have habs1ms : |s - 1| ≤ 1 := by
    have h1 : |s - 1| * Δ ≤ 1 * Δ := by
      rw [one_mul]; linarith [hbd_eq ▸ hbd]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have habs_st : |s - t| = 1 := by
    have h1 : |s - t| * Δ = 1 * Δ := by rw [one_mul, ← hcd_eq]; exact hcd
    exact mul_right_cancel₀ (ne_of_gt hΔ_pos) h1
  have ht_le1 : t ≤ 1 := (abs_le.mp habst).2
  have hneg1mt_le1 : -(1:ℝ) ≤ t - 1 := (abs_le.mp habs1mt).1
  have ht_nn : 0 ≤ t := by linarith
  have hs_le1 : s ≤ 1 := (abs_le.mp habss).2
  have hneg1ms_le1 : -(1:ℝ) ≤ s - 1 := (abs_le.mp habs1ms).1
  have hs_nn : 0 ≤ s := by linarith
  have h_st_diff : s - t = 1 ∨ s - t = -1 :=
    (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp habs_st
  rcases h_st_diff with hd | hd
  · have ht0 : t = 0 := by linarith
    have _hs1 : s = 1 := by linarith
    have hca : c = a := by
      ext i; have := ht i; rw [ht0] at this; linarith
    exact h_ac hca.symm
  · have ht1 : t = 1 := by linarith
    have _hs0 : s = 0 := by linarith
    have hcb : c = b := by
      ext i; have := ht i; rw [ht1] at this; linarith
    exact h_bc hcb.symm

/-- The older separated-case theorem follows immediately from the sharper
collinear endpoint contradiction by ignoring the disjointness field. -/
theorem collinearSeparatedDiameterContradiction :
    CollinearSeparatedDiameterContradiction := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hCol
  exact collinearDiameterEndpointContradiction a b c d Δ
    h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hCol.1 hCol.2.1

/-- Unified separated-diameter contradiction: no separated-segment certificate
(proper or collinear) can coexist with the diameter equalities and all four
cross-distance upper bounds. -/
def SeparatedDiameterContradiction : Prop :=
  ∀ (a b c d : Point2) (Δ : ℝ),
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    dist a b = Δ →
    dist c d = Δ →
    dist a c ≤ Δ →
    dist a d ≤ Δ →
    dist b c ≤ Δ →
    dist b d ≤ Δ →
    (ProperSegmentSeparation a b c d ∨ CollinearSegmentSeparation a b c d) →
      False

/-- The unified separated-diameter contradiction supplies the proper case. -/
theorem proper_contradiction_from_separated_diameter
    (h : SeparatedDiameterContradiction) :
    ProperSeparatedDiameterContradiction := by
  intro a b c d Δ hac had hbc hbd hab hcd hac_le had_le hbc_le hbd_le hproper
  exact h a b c d Δ hac had hbc hbd hab hcd hac_le had_le hbc_le hbd_le
    (Or.inl hproper)

/-- The unified separated-diameter contradiction supplies the collinear case. -/
theorem collinear_contradiction_from_separated_diameter
    (h : SeparatedDiameterContradiction) :
    CollinearSeparatedDiameterContradiction := by
  intro a b c d Δ hac had hbc hbd hab hcd hac_le had_le hbc_le hbd_le hcol
  exact h a b c d Δ hac had hbc hbd hab hcd hac_le had_le hbc_le hbd_le
    (Or.inr hcol)

/-- Segment-separation plus the unified separated-diameter contradiction prove
the four-point crossing lemma. -/
theorem four_point_diameter_crossing_from_separated_diameter
    (hSep : DisjointSegmentsHaveSeparation)
    (hContr : SeparatedDiameterContradiction) :
    FourPointDiameterCrossing := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd
  by_cases hmeet : OrderedEdgesMeetGeometrically (a, b) (c, d)
  · exact hmeet
  · exfalso
    have hdisj : OrderedEdgesGeometricallyDisjoint (a, b) (c, d) := hmeet
    exact hContr a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd
      (hSep a b c d h_ac h_ad h_bc h_bd hdisj)

/-- The segment-separation case split plus the two separated-diameter
contradictions prove the four-point crossing lemma.  All easy endpoint-sharing
and Δ = 0 cases have already been discharged elsewhere; this theorem handles
the remaining proof route by contradiction from geometric disjointness. -/
theorem four_point_diameter_crossing_from_separation_bridges
    (hSep : DisjointSegmentsHaveSeparation)
    (hProper : ProperSeparatedDiameterContradiction)
    (hCollinear : CollinearSeparatedDiameterContradiction) :
    FourPointDiameterCrossing := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd
  by_cases hmeet : OrderedEdgesMeetGeometrically (a, b) (c, d)
  · exact hmeet
  · exfalso
    have hdisj : OrderedEdgesGeometricallyDisjoint (a, b) (c, d) := hmeet
    rcases hSep a b c d h_ac h_ad h_bc h_bd hdisj with hProperSep | hColSep
    · exact hProper a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hProperSep
    · exact hCollinear a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hColSep

/-- The four-point crossing lemma implies the endpoint-disjoint local meeting
bridge.  All four cross-distances are at most the diameter by `IsDiameterShell`,
and endpoint-disjointness is precisely the four `≠` hypotheses. -/
theorem endpoint_disjoint_local_meeting_from_four_point
    (h4 : FourPointDiameterCrossing) :
    EndpointDisjointDiameterSegmentsMeetLocally := by
  filter_upwards with n
  intro A _hA Δ hΔ e he f hf hShare
  classical
  -- Unpack `e ∈ diameterOrderedEdges A Δ`.
  have heFilter := Finset.mem_filter.mp he
  have heDist : dist e.1 e.2 = Δ := heFilter.2
  have heEvents := Finset.mem_filter.mp heFilter.1
  have heProd := Finset.mem_product.mp heEvents.1
  have he1A : e.1 ∈ A := heProd.1
  have he2A : e.2 ∈ A := heProd.2
  -- Unpack `f ∈ diameterOrderedEdges A Δ`.
  have hfFilter := Finset.mem_filter.mp hf
  have hfDist : dist f.1 f.2 = Δ := hfFilter.2
  have hfEvents := Finset.mem_filter.mp hfFilter.1
  have hfProd := Finset.mem_product.mp hfEvents.1
  have hf1A : f.1 ∈ A := hfProd.1
  have hf2A : f.2 ∈ A := hfProd.2
  -- Endpoint-disjointness from `¬ OrderedEdgesShareEndpoint e f`.
  have h13 : e.1 ≠ f.1 := fun hk => hShare (Or.inl hk)
  have h14 : e.1 ≠ f.2 := fun hk => hShare (Or.inr (Or.inl hk))
  have h23 : e.2 ≠ f.1 := fun hk => hShare (Or.inr (Or.inr (Or.inl hk)))
  have h24 : e.2 ≠ f.2 := fun hk => hShare (Or.inr (Or.inr (Or.inr hk)))
  -- All four cross-distances lie in the ordered distance spectrum, so they are
  -- bounded by the diameter `Δ`.
  have hΔmax : ∀ s ∈ orderedDistanceSpectrum A, s ≤ Δ := hΔ.2
  have hSpec : ∀ x y : Point2,
      x ∈ A → y ∈ A → x ≠ y → dist x y ∈ orderedDistanceSpectrum A := by
    intro x y hxA hyA hxy
    unfold orderedDistanceSpectrum
    refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
    unfold orderedPairEvents
    refine Finset.mem_filter.mpr ⟨?_, hxy⟩
    exact Finset.mem_product.mpr ⟨hxA, hyA⟩
  have hd13 : dist e.1 f.1 ≤ Δ := hΔmax _ (hSpec _ _ he1A hf1A h13)
  have hd14 : dist e.1 f.2 ≤ Δ := hΔmax _ (hSpec _ _ he1A hf2A h14)
  have hd23 : dist e.2 f.1 ≤ Δ := hΔmax _ (hSpec _ _ he2A hf1A h23)
  have hd24 : dist e.2 f.2 ≤ Δ := hΔmax _ (hSpec _ _ he2A hf2A h24)
  -- Apply the universal four-point lemma.
  exact h4 e.1 e.2 f.1 f.2 Δ h13 h14 h23 h24 heDist hfDist hd13 hd14 hd23 hd24

/-- The local diameter-segment intersection lemma implies the no-disjoint
diameter-edge bridge. -/
theorem no_disjoint_diameter_edges_from_local_meeting
    (hMeet : DiameterSegmentsMeetLocally) :
    NoDisjointDiameterEdges := by
  filter_upwards [hMeet] with n hMeetN
  intro A hA Δ hΔ e he f hf hDisj
  exact hDisj (hMeetN A hA Δ hΔ e he f hf)

/-- Ordered straight-line thrackle bound: any ordered edge set on `A` with no
geometrically disjoint pairs has at most `2|A|` directed edges.  The factor `2`
matches the ordered-pair normalization. -/
def OrderedThrackleBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ E : Finset (Point2 × Point2),
          (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
          (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
            E.card ≤ 2 * A.card

/-- Forget orientation of an ordered edge. -/
def unorderedEdgeOfOrdered (e : Point2 × Point2) : Sym2 Point2 :=
  Sym2.mk e

/-- Reversing an ordered representative does not change its unordered edge. -/
theorem unorderedEdgeOfOrdered_swap (e : Point2 × Point2) :
    unorderedEdgeOfOrdered e.swap = unorderedEdgeOfOrdered e := by
  cases e with
  | mk a b =>
    unfold unorderedEdgeOfOrdered
    exact (Sym2.mk_eq_mk_iff).mpr (Or.inr rfl)

/-- Undirected support of an ordered edge set. -/
noncomputable def unorderedEdgeSupport (E : Finset (Point2 × Point2)) :
    Finset (Sym2 Point2) := by
  classical
  exact E.image unorderedEdgeOfOrdered

/-- Membership in the unordered support is exactly the existence of an ordered
representative in the original edge set. -/
theorem mem_unorderedEdgeSupport_iff
    {E : Finset (Point2 × Point2)} {u : Sym2 Point2} :
    u ∈ unorderedEdgeSupport E ↔
      ∃ e ∈ E, unorderedEdgeOfOrdered e = u := by
  classical
  simp [unorderedEdgeSupport]

/-- Two unordered support edges have geometrically disjoint representatives if
some ordered representatives in `E` are geometrically disjoint. -/
def SupportEdgesHaveDisjointRepresentatives
    (E : Finset (Point2 × Point2)) (u v : Sym2 Point2) : Prop :=
  ∃ e ∈ E, ∃ f ∈ E,
    unorderedEdgeOfOrdered e = u ∧
    unorderedEdgeOfOrdered f = v ∧
    OrderedEdgesGeometricallyDisjoint e f

/-- A support-level disjoint pair immediately yields the ordered pair required
by the thrackle obstruction. -/
theorem ordered_disjoint_pair_of_support_disjoint_pair
    {E : Finset (Point2 × Point2)} {u v : Sym2 Point2}
    (h : SupportEdgesHaveDisjointRepresentatives E u v) :
    ∃ e ∈ E, ∃ f ∈ E, OrderedEdgesGeometricallyDisjoint e f := by
  rcases h with ⟨e, he, f, hf, _heu, _hfv, hDisj⟩
  exact ⟨e, he, f, hf, hDisj⟩

/-- The finite orientation-fiber condition: after forgetting orientation, each
undirected edge has at most two directed representatives in `E`.  This is pure
bookkeeping, separated so it can later be proved once we choose the preferred
`Sym2` API for unordered edges. -/
def OrientationFiberAtMostTwo (E : Finset (Point2 × Point2)) : Prop :=
  ∀ u ∈ unorderedEdgeSupport E,
    ((E.filter (fun e => unorderedEdgeOfOrdered e = u)).card) ≤ 2

/-- Orientation fibers are universally bounded by two: an unordered pair has at
most the two directed representatives `(a,b)` and `(b,a)`. -/
theorem orientation_fiber_at_most_two (E : Finset (Point2 × Point2)) :
    OrientationFiberAtMostTwo E := by
  classical
  intro u hu
  unfold unorderedEdgeSupport at hu
  rw [Finset.mem_image] at hu
  rcases hu with ⟨e0, _he0, he0u⟩
  let T : Finset (Point2 × Point2) := {e0, e0.swap}
  have hsub : (E.filter (fun e => unorderedEdgeOfOrdered e = u)) ⊆ T := by
    intro e he
    have heu : unorderedEdgeOfOrdered e = u := (Finset.mem_filter.mp he).2
    have hmk : Sym2.mk e = Sym2.mk e0 := by
      unfold unorderedEdgeOfOrdered at heu he0u
      rw [heu, he0u]
    have hcases := Sym2.mk_eq_mk_iff.mp hmk
    rcases hcases with hEq | hSwap
    · subst hEq
      simp [T]
    · subst hSwap
      simp [T]
  calc
    (E.filter (fun e => unorderedEdgeOfOrdered e = u)).card ≤ T.card :=
      Finset.card_le_card hsub
    _ ≤ 2 := by
      unfold T
      exact Finset.card_le_two

/-- Pure finite bookkeeping: if every orientation fiber has size at most two,
then the ordered edge set has at most twice its undirected support. -/
theorem ordered_card_le_two_mul_unordered_support
    (E : Finset (Point2 × Point2))
    (hFib : OrientationFiberAtMostTwo E) :
    E.card ≤ 2 * (unorderedEdgeSupport E).card := by
  classical
  let f : Point2 × Point2 → Sym2 Point2 := unorderedEdgeOfOrdered
  have hMaps :
      Set.MapsTo f ↑E ↑(unorderedEdgeSupport E) := by
    intro e he
    unfold unorderedEdgeSupport f
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hFiber :=
    Finset.card_eq_sum_card_fiberwise
      (s := E)
      (t := unorderedEdgeSupport E)
      (f := f) hMaps
  rw [hFiber]
  calc
    (∑ u ∈ unorderedEdgeSupport E, {a ∈ E | f a = u}.card)
        ≤ ∑ _u ∈ unorderedEdgeSupport E, 2 := by
          apply Finset.sum_le_sum
          intro u hu
          simpa [f, OrientationFiberAtMostTwo] using hFib u hu
    _ = 2 * (unorderedEdgeSupport E).card := by
          simp [Finset.sum_const, mul_comm]

/-- Two ordered edges meet simply if their closed segments share exactly one
point.  The Conway straight-line thrackle theorem counts edges under this
condition; it excludes overlapping collinear segments that can inflate the
pairwise-meeting count past `|A|`. -/
def OrderedEdgesMeetSimply (e f : Point2 × Point2) : Prop :=
  ∃! x : Point2, OnClosedSegment e.1 e.2 x ∧ OnClosedSegment f.1 f.2 x

/-- Simple meeting is symmetric in the two ordered edges. -/
theorem ordered_edges_meet_simply_symm
    {e f : Point2 × Point2} (h : OrderedEdgesMeetSimply e f) :
    OrderedEdgesMeetSimply f e := by
  rcases h with ⟨x, hx, huniq⟩
  refine ⟨x, ⟨hx.2, hx.1⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.2, hy.1⟩

/-- Symmetric iff form of simple meeting. -/
theorem ordered_edges_meet_simply_comm (e f : Point2 × Point2) :
    OrderedEdgesMeetSimply e f ↔ OrderedEdgesMeetSimply f e :=
  ⟨ordered_edges_meet_simply_symm, ordered_edges_meet_simply_symm⟩

/-- Swapping the first edge's orientation preserves simple meeting. -/
theorem ordered_edges_meet_simply_swap_left
    {a b : Point2} {f : Point2 × Point2}
    (h : OrderedEdgesMeetSimply (a, b) f) :
    OrderedEdgesMeetSimply (b, a) f := by
  rcases h with ⟨x, hx, huniq⟩
  refine ⟨x, ⟨on_closed_segment_symm hx.1, hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨on_closed_segment_symm hy.1, hy.2⟩

/-- Swapping the second edge's orientation preserves simple meeting. -/
theorem ordered_edges_meet_simply_swap_right
    {e : Point2 × Point2} {c d : Point2}
    (h : OrderedEdgesMeetSimply e (c, d)) :
    OrderedEdgesMeetSimply e (d, c) := by
  rcases h with ⟨x, hx, huniq⟩
  refine ⟨x, ⟨hx.1, on_closed_segment_symm hx.2⟩, ?_⟩
  intro y hy
  exact huniq y ⟨hy.1, on_closed_segment_symm hy.2⟩

/-- Swapping both edge orientations preserves simple meeting. -/
theorem ordered_edges_meet_simply_swap_both
    {a b c d : Point2}
    (h : OrderedEdgesMeetSimply (a, b) (c, d)) :
    OrderedEdgesMeetSimply (b, a) (d, c) :=
  ordered_edges_meet_simply_swap_right
    (ordered_edges_meet_simply_swap_left h)

/-- Simple meeting implies geometric meeting. -/
theorem ordered_edges_meet_of_meet_simply
    {e f : Point2 × Point2} (h : OrderedEdgesMeetSimply e f) :
    OrderedEdgesMeetGeometrically e f := by
  rcases h with ⟨x, hx, _huniq⟩
  exact ⟨x, hx⟩

/-- Simple meeting only depends on the unordered edge classes, not on the chosen
orientation of each ordered representative. -/
theorem ordered_edges_meet_simply_of_same_unordered
    {e e₀ f f₀ : Point2 × Point2}
    (he : unorderedEdgeOfOrdered e = unorderedEdgeOfOrdered e₀)
    (hf : unorderedEdgeOfOrdered f = unorderedEdgeOfOrdered f₀)
    (h : OrderedEdgesMeetSimply e₀ f₀) :
    OrderedEdgesMeetSimply e f := by
  unfold unorderedEdgeOfOrdered at he hf
  have hecases := Sym2.mk_eq_mk_iff.mp he
  have hfcases := Sym2.mk_eq_mk_iff.mp hf
  rcases hecases with heq | hswap <;> rcases hfcases with hfeq | hfswap
  · subst heq
    subst hfeq
    exact h
  · subst heq
    subst hfswap
    exact ordered_edges_meet_simply_swap_right h
  · subst hswap
    subst hfeq
    exact ordered_edges_meet_simply_swap_left h
  · subst hswap
    subst hfswap
    exact ordered_edges_meet_simply_swap_both h

/-- A pairwise-simply-meeting edge system is a Conway straight-line thrackle:
every pair of distinct edges shares exactly one point (shared endpoint or
proper crossing). -/
def IsConwayThrackle (E : Finset (Point2 × Point2)) : Prop :=
  ∀ e ∈ E, ∀ f ∈ E, e ≠ f → OrderedEdgesMeetSimply e f

/-- Support-level simple meeting: two unordered support edges have ordered
representatives in `E` whose closed segments share exactly one point.  This is
the right formulation for ordered edge sets that contain both orientations of
the same undirected edge. -/
def SupportEdgesMeetSimply
    (E : Finset (Point2 × Point2)) (u v : Sym2 Point2) : Prop :=
  ∃ e ∈ E, ∃ f ∈ E,
    unorderedEdgeOfOrdered e = u ∧
    unorderedEdgeOfOrdered f = v ∧
    OrderedEdgesMeetSimply e f

/-- Ordered representatives that meet simply give simple meeting of their
unordered support classes. -/
theorem support_edges_meet_simply_of_ordered_representatives
    {E : Finset (Point2 × Point2)} {e f : Point2 × Point2}
    (he : e ∈ E) (hf : f ∈ E)
    (hSimple : OrderedEdgesMeetSimply e f) :
    SupportEdgesMeetSimply E (unorderedEdgeOfOrdered e) (unorderedEdgeOfOrdered f) :=
  ⟨e, he, f, hf, rfl, rfl, hSimple⟩

/-- The support-level simple-meeting relation is symmetric. -/
theorem support_edges_meet_simply_symm
    {E : Finset (Point2 × Point2)} {u v : Sym2 Point2}
    (h : SupportEdgesMeetSimply E u v) :
    SupportEdgesMeetSimply E v u := by
  rcases h with ⟨e, he, f, hf, heu, hfv, hSimple⟩
  exact ⟨f, hf, e, he, hfv, heu, ordered_edges_meet_simply_symm hSimple⟩

/-- Chosen ordered representative for one unordered support edge. -/
noncomputable def chosenSupportRepresentative
    (E : Finset (Point2 × Point2))
    (u : {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E}) :
    Point2 × Point2 :=
  Classical.choose (mem_unorderedEdgeSupport_iff.mp u.2)

/-- The chosen representative belongs to the original ordered edge set. -/
theorem chosenSupportRepresentative_mem
    (E : Finset (Point2 × Point2))
    (u : {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E}) :
    chosenSupportRepresentative E u ∈ E :=
  (Classical.choose_spec (mem_unorderedEdgeSupport_iff.mp u.2)).1

/-- The chosen representative has the required unordered support class. -/
theorem chosenSupportRepresentative_unordered
    (E : Finset (Point2 × Point2))
    (u : {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E}) :
    unorderedEdgeOfOrdered (chosenSupportRepresentative E u) = u.1 :=
  (Classical.choose_spec (mem_unorderedEdgeSupport_iff.mp u.2)).2

/-- One chosen ordered representative per unordered support edge. -/
noncomputable def chosenOrderedSupport (E : Finset (Point2 × Point2)) :
    Finset (Point2 × Point2) := by
  classical
  exact (unorderedEdgeSupport E).attach.image (chosenSupportRepresentative E)

/-- Chosen support representatives are drawn from the original ordered edge
set. -/
theorem chosenOrderedSupport_subset
    (E : Finset (Point2 × Point2)) :
    chosenOrderedSupport E ⊆ E := by
  classical
  intro e he
  unfold chosenOrderedSupport at he
  rw [Finset.mem_image] at he
  rcases he with ⟨u, _hu, rfl⟩
  exact chosenSupportRepresentative_mem E u

/-- The chosen representative set has exactly the same unordered support as the
original ordered edge set. -/
theorem unorderedEdgeSupport_chosenOrderedSupport
    (E : Finset (Point2 × Point2)) :
    unorderedEdgeSupport (chosenOrderedSupport E) = unorderedEdgeSupport E := by
  classical
  ext u
  constructor
  · intro hu
    rcases (mem_unorderedEdgeSupport_iff.mp hu) with ⟨e, he, heu⟩
    exact mem_unorderedEdgeSupport_iff.mpr
      ⟨e, chosenOrderedSupport_subset E he, heu⟩
  · intro hu
    let usub : {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} := ⟨u, hu⟩
    apply mem_unorderedEdgeSupport_iff.mpr
    refine ⟨chosenSupportRepresentative E usub, ?_, ?_⟩
    · unfold chosenOrderedSupport
      rw [Finset.mem_image]
      exact ⟨usub, Finset.mem_attach _ _, rfl⟩
    · exact chosenSupportRepresentative_unordered E usub

/-- Chosen representatives are injective as a map from unordered support classes
to ordered representatives. -/
theorem chosenSupportRepresentative_injective
    (E : Finset (Point2 × Point2)) :
    Function.Injective (chosenSupportRepresentative E) := by
  intro u v huv
  apply Subtype.ext
  have hu := chosenSupportRepresentative_unordered E u
  have hv := chosenSupportRepresentative_unordered E v
  calc
    u.1 = unorderedEdgeOfOrdered (chosenSupportRepresentative E u) := hu.symm
    _ = unorderedEdgeOfOrdered (chosenSupportRepresentative E v) := by rw [huv]
    _ = v.1 := hv

/-- The chosen representative finset has the same cardinality as the unordered
support. -/
theorem chosenOrderedSupport_card
    (E : Finset (Point2 × Point2)) :
    (chosenOrderedSupport E).card = (unorderedEdgeSupport E).card := by
  classical
  unfold chosenOrderedSupport
  rw [Finset.card_image_of_injective]
  · simp
  · exact chosenSupportRepresentative_injective E

/-- Conway condition on unordered support.  This is the correct condition for
diameter edge sets, because `diameterOrderedEdges` contains both orientations
of every edge and therefore cannot be a Conway thrackle as an ordered finset. -/
def IsConwayThrackleSupport (E : Finset (Point2 × Point2)) : Prop :=
  ∀ u ∈ unorderedEdgeSupport E,
    ∀ v ∈ unorderedEdgeSupport E,
      u ≠ v → SupportEdgesMeetSimply E u v

/-- Support-level Conway condition promotes to the ordinary ordered Conway
condition on the chosen representative finset. -/
theorem isConwayThrackle_chosenOrderedSupport
    {E : Finset (Point2 × Point2)}
    (hSupport : IsConwayThrackleSupport E) :
    IsConwayThrackle (chosenOrderedSupport E) := by
  classical
  intro e he f hf hef
  unfold chosenOrderedSupport at he hf
  rw [Finset.mem_image] at he
  rw [Finset.mem_image] at hf
  rcases he with ⟨u, _hu, rfl⟩
  rcases hf with ⟨v, _hv, rfl⟩
  have huv : u.1 ≠ v.1 := by
    intro hval
    exact hef (congrArg (chosenSupportRepresentative E) (Subtype.ext hval))
  rcases hSupport u.1 u.2 v.1 v.2 huv with
    ⟨e₀, _he₀, f₀, _hf₀, he₀u, hf₀v, hSimple⟩
  exact ordered_edges_meet_simply_of_same_unordered
    (by rw [chosenSupportRepresentative_unordered E u, he₀u])
    (by rw [chosenSupportRepresentative_unordered E v, hf₀v])
    hSimple

/-- Conway straight-line thrackle support bound: if every pair of edges meets
simply, the undirected support has at most `|A|` edges.  This is the correct
Lovász-Pach-Szegedy / Cairns-Nikolayevsky counting theorem.  The bound is
false without the "simply" condition (collinear overlapping counterexample). -/
def ConwayThrackleSupportBound : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackle E →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Constructive form of the Conway straight-line thrackle theorem: for each
finite straight-line Conway thrackle, charge each unordered edge injectively to
one ambient vertex.  This is equivalent in finite cardinality terms, but is the
right target for a future formal proof of the classical theorem. -/
def ConwayThrackleEndpointChargeCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackle E →
        ∃ charge :
          {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
            Function.Injective charge

/-- An injective endpoint charge proves the standard ordered Conway support
bound by finite cardinality. -/
theorem conway_support_bound_from_endpoint_charge
    (hCharge : ConwayThrackleEndpointChargeCertificate) :
    ConwayThrackleSupportBound := by
  intro A E hEdges hConway
  obtain ⟨charge, hInjective⟩ := hCharge A E hEdges hConway
  have hcard := Fintype.card_le_of_injective charge hInjective
  simpa using hcard

/-- Support-level Conway straight-line thrackle support bound.  This is the
correct theorem surface for ordered finsets that may contain both orientations
of an undirected edge. -/
def ConwayThrackleSupportBoundOnSupport : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackleSupport E →
        (unorderedEdgeSupport E).card ≤ A.card

/-- The standard ordered Conway thrackle theorem implies the support-level form:
choose one ordered representative for each unordered support edge, apply the
standard theorem to that chosen representative system, then transfer the support
cardinality back. -/
theorem conway_support_bound_on_support_from_ordered
    (hConway : ConwayThrackleSupportBound) :
    ConwayThrackleSupportBoundOnSupport := by
  intro A E hEdges hSupport
  have hChosenEdges :
      ∀ e ∈ chosenOrderedSupport E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2 := by
    intro e he
    exact hEdges e (chosenOrderedSupport_subset E he)
  have hCard :
      (unorderedEdgeSupport (chosenOrderedSupport E)).card ≤ A.card :=
    hConway A (chosenOrderedSupport E) hChosenEdges
      (isConwayThrackle_chosenOrderedSupport hSupport)
  simpa [unorderedEdgeSupport_chosenOrderedSupport E] using hCard

/-- Undirected straight-line thrackle support bound: if an ordered edge set has
no geometrically disjoint pairs, then its undirected support has at most `|A|`
edges.  This is the Perles/Hopf-Pannwitz geometric theorem in its clean
undirected form.

**Caveat (2026-05-22):** This bound is stated for the set-theoretic meeting
predicate (`OrderedEdgesMeetGeometrically`), which allows overlapping segments.
For collinear point sets the bound is FALSE in this form. The correct
classical statement uses the Conway thrackle condition
(`ConwayThrackleSupportBound`). For the Erdős #132 application via diameter
segments, the Conway condition is automatically satisfied because distinct
diameter segments never overlap (proved by collinear analysis in
`collinearSeparatedDiameterContradiction`). -/
def UndirectedThrackleSupportBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ E : Finset (Point2 × Point2),
          (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
          (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
            (unorderedEdgeSupport E).card ≤ A.card

/-- The Conway support bound implies the general undirected support bound for
any edge system that happens to be a Conway thrackle, because simple meeting
implies non-disjointness. -/
theorem undirected_thrackle_support_of_conway_thrackle
    (hConway : ConwayThrackleSupportBound)
    (A : Finset Point2) (E : Finset (Point2 × Point2))
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2)
    (hSimple : IsConwayThrackle E) :
    (unorderedEdgeSupport E).card ≤ A.card :=
  hConway A E hEdges hSimple

/-- Diameter-specific ordered thrackle bound.  The diameter structure guarantees
the Conway condition via the four-point crossing geometry.  This is the correct
classical target for the Hopf-Pannwitz counting step. -/
def DiameterConwayThrackleBound : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        orderedShellMultiplicity A Δ ≤ 2 * A.card

/-- Legacy ordered formulation.  This is intentionally kept only as a warning
surface: it is false for `diameterOrderedEdges`, because the ordered finset
contains both `(a,b)` and `(b,a)` and those two distinct ordered edges have the
same segment.  Use `DiameterEdgeSupportFormsConwayThrackle` instead. -/
def DiameterEdgesFormConwayThrackle : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        IsConwayThrackle (diameterOrderedEdges A Δ)

/-- Correct diameter Conway condition, stated on unordered support rather than
the ordered representative finset. -/
def DiameterEdgeSupportFormsConwayThrackle : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        IsConwayThrackleSupport (diameterOrderedEdges A Δ)

/-- Local representative form of the diameter-support Conway condition.  This is
the geometric statement left after removing ordered-orientation duplicates:
distinct unordered diameter support edges have ordered representatives whose
segments meet in exactly one point. -/
def DiameterSupportSimpleRepresentativeCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ u ∈ unorderedEdgeSupport (diameterOrderedEdges A Δ),
          ∀ v ∈ unorderedEdgeSupport (diameterOrderedEdges A Δ),
            u ≠ v →
              SupportEdgesMeetSimply (diameterOrderedEdges A Δ) u v

/-- Ordered-representative form of the diameter-support Conway condition.  This
is the sharp local geometry left on the diameter side: any two ordered diameter
representatives of distinct unordered support edges meet in exactly one point. -/
def DistinctDiameterRepresentativesMeetSimply : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ e ∈ diameterOrderedEdges A Δ,
          ∀ f ∈ diameterOrderedEdges A Δ,
            unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f →
              OrderedEdgesMeetSimply e f

/-- Distinct unordered representatives are distinct ordered edges.  This removes
the orientation-duplicate pathology from the local diameter representative
target. -/
theorem ordered_edges_ne_of_unorderedEdgeOfOrdered_ne
    {e f : Point2 × Point2}
    (h : unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f) :
    e ≠ f := by
  intro hef
  exact h (by rw [hef])

/-- Endpoint-sharing part of the local diameter representative theorem. -/
def SharedEndpointDiameterRepresentativesMeetSimply : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ e ∈ diameterOrderedEdges A Δ,
          ∀ f ∈ diameterOrderedEdges A Δ,
            unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f →
              OrderedEdgesShareEndpoint e f →
                OrderedEdgesMeetSimply e f

/-- Endpoint-disjoint part of the local diameter representative theorem. -/
def EndpointDisjointDiameterRepresentativesMeetSimply : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ e ∈ diameterOrderedEdges A Δ,
          ∀ f ∈ diameterOrderedEdges A Δ,
            unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f →
              ¬ OrderedEdgesShareEndpoint e f →
                OrderedEdgesMeetSimply e f

/-- Uniqueness-only form of the endpoint-disjoint diameter representative
geometry.  Existence of an intersection is already supplied by
`fourPointDiameterCrossing_thm`; this certificate says that two endpoint-disjoint
diameter representatives cannot overlap in more than one point. -/
def EndpointDisjointDiameterIntersectionUniqueCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ e ∈ diameterOrderedEdges A Δ,
          ∀ f ∈ diameterOrderedEdges A Δ,
            unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f →
              ¬ OrderedEdgesShareEndpoint e f →
                ∀ x y : Point2,
                  (OnClosedSegment e.1 e.2 x ∧ OnClosedSegment f.1 f.2 x) →
                  (OnClosedSegment e.1 e.2 y ∧ OnClosedSegment f.1 f.2 y) →
                    x = y

/-- The only remaining geometric content behind endpoint-disjoint uniqueness:
if two endpoint-disjoint diameter representatives have two distinct common
points, then the second representative's endpoints lie on the line through the
first representative. -/
def EndpointDisjointTwoPointIntersectionForcesCollinear : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        ∀ e ∈ diameterOrderedEdges A Δ,
          ∀ f ∈ diameterOrderedEdges A Δ,
            unorderedEdgeOfOrdered e ≠ unorderedEdgeOfOrdered f →
              ¬ OrderedEdgesShareEndpoint e f →
                ∀ x y : Point2,
                  x ≠ y →
                  (OnClosedSegment e.1 e.2 x ∧ OnClosedSegment f.1 f.2 x) →
                  (OnClosedSegment e.1 e.2 y ∧ OnClosedSegment f.1 f.2 y) →
                    orient2 e.1 e.2 f.1 = 0 ∧ orient2 e.1 e.2 f.2 = 0

/-- The two-point intersection collinearity certificate is pure affine
incidence: two distinct common points determine a line, so both endpoint-disjoint
diameter representatives lie on that same line. -/
theorem endpoint_disjoint_two_point_intersection_forces_collinear :
    EndpointDisjointTwoPointIntersectionForcesCollinear := by
  intro A Δ hΔ e he f hf hUne hNoShare x y hxy hx hy
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  have hx_ab : orient2 a b x = 0 := orient2_eq_zero_of_on_closed_segment hx.1
  have hy_ab : orient2 a b y = 0 := orient2_eq_zero_of_on_closed_segment hy.1
  have hx_cd : orient2 c d x = 0 := orient2_eq_zero_of_on_closed_segment hx.2
  have hy_cd : orient2 c d y = 0 := orient2_eq_zero_of_on_closed_segment hy.2
  have hcd_ne : c ≠ d := by
    rcases diameter_ordered_edge_data hf with ⟨_, _, hne, _⟩
    simpa using hne
  have hdc_ne : d ≠ c := hcd_ne.symm
  have h_cxy : orient2 x y c = 0 := by
    have htmp : orient2 c x y = 0 :=
      orient2_zero_transitive_swap hcd_ne hx_cd hy_cd
    simpa [orient2_cyclic] using htmp
  have h_dxy : orient2 x y d = 0 := by
    have hx_dc : orient2 d c x = 0 := by
      rw [orient2_swap₁₂]
      simp [hx_cd]
    have hy_dc : orient2 d c y = 0 := by
      rw [orient2_swap₁₂]
      simp [hy_cd]
    have htmp : orient2 d x y = 0 :=
      orient2_zero_transitive_swap hdc_ne hx_dc hy_dc
    simpa [orient2_cyclic] using htmp
  exact ⟨
    orient2_zero_of_two_points_on_line_and_point_on_join hxy hx_ab hy_ab h_cxy,
    orient2_zero_of_two_points_on_line_and_point_on_join hxy hx_ab hy_ab h_dxy⟩

/-- If two common points force collinearity, then endpoint-disjoint diameter
intersections are unique: otherwise the sharper collinear diameter endpoint
contradiction applies. -/
theorem endpoint_disjoint_diameter_intersection_unique_from_two_point_collinear
    (hCol : EndpointDisjointTwoPointIntersectionForcesCollinear) :
    EndpointDisjointDiameterIntersectionUniqueCertificate := by
  intro A Δ hΔ e he f hf hUne hNoShare x y hx hy
  by_contra hxy
  have hxy_ne : x ≠ y := by exact fun h => hxy h
  rcases hCol A Δ hΔ e he f hf hUne hNoShare x y hxy_ne hx hy with
    ⟨hcol1, hcol2⟩
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  rcases diameter_ordered_edges_cross_distances_le hΔ he hf with
    ⟨hab, hcd, hac, had, hbc, hbd⟩
  unfold OrderedEdgesShareEndpoint at hNoShare
  simp at hNoShare hcol1 hcol2
  have h_ac : a ≠ c := hNoShare.1
  have h_ad : a ≠ d := hNoShare.2.1
  have h_bc : b ≠ c := hNoShare.2.2.1
  have h_bd : b ≠ d := hNoShare.2.2.2
  exact collinearDiameterEndpointContradiction a b c d Δ
    h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd hcol1 hcol2

/-- The shared-endpoint and endpoint-disjoint local diameter representative
lemmas combine to give the full ordered-representative certificate. -/
theorem distinct_diameter_representatives_meet_simply_from_cases
    (hShared : SharedEndpointDiameterRepresentativesMeetSimply)
    (hDisjoint : EndpointDisjointDiameterRepresentativesMeetSimply) :
    DistinctDiameterRepresentativesMeetSimply := by
  intro A Δ hΔ e he f hf hne
  by_cases hShare : OrderedEdgesShareEndpoint e f
  · exact hShared A Δ hΔ e he f hf hne hShare
  · exact hDisjoint A Δ hΔ e he f hf hne hShare

/-- The ordered-representative simple-meeting certificate supplies the
support-level representative certificate by choosing representatives of the two
unordered support edges. -/
theorem diameter_support_simple_representatives_from_ordered_representatives
    (h : DistinctDiameterRepresentativesMeetSimply) :
    DiameterSupportSimpleRepresentativeCertificate := by
  intro A Δ hΔ u hu v hv huv
  rcases (mem_unorderedEdgeSupport_iff.mp hu) with ⟨e, he, heu⟩
  rcases (mem_unorderedEdgeSupport_iff.mp hv) with ⟨f, hf, hfv⟩
  refine ⟨e, he, f, hf, heu, hfv, ?_⟩
  apply h A Δ hΔ e he f hf
  intro hsame
  apply huv
  rw [← heu, ← hfv]
  exact hsame

/-- The local representative certificate is exactly enough to show that diameter
support forms a Conway thrackle. -/
theorem diameter_support_forms_conway_from_simple_representatives
    (h : DiameterSupportSimpleRepresentativeCertificate) :
    DiameterEdgeSupportFormsConwayThrackle := by
  intro A Δ hΔ u hu v hv huv
  exact h A Δ hΔ u hu v hv huv

/-- Support-level Conway support plus the diameter support Conway condition
gives the diameter-specific ordered multiplicity bound. -/
theorem diameter_conway_bound_from_support_conway
    (hSupport : ConwayThrackleSupportBoundOnSupport)
    (hDiam : DiameterEdgeSupportFormsConwayThrackle) :
    DiameterConwayThrackleBound := by
  intro A Δ hΔ
  have hEdges :
      ∀ e ∈ diameterOrderedEdges A Δ,
        e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2 := by
    intro e he
    rcases diameter_ordered_edge_data he with ⟨he1, he2, hne, _hdist⟩
    exact ⟨he1, he2, hne⟩
  have hOrdered :
      (diameterOrderedEdges A Δ).card ≤
        2 * (unorderedEdgeSupport (diameterOrderedEdges A Δ)).card :=
    ordered_card_le_two_mul_unordered_support
      (diameterOrderedEdges A Δ)
      (orientation_fiber_at_most_two (diameterOrderedEdges A Δ))
  have hSupportCard :
      (unorderedEdgeSupport (diameterOrderedEdges A Δ)).card ≤ A.card :=
    hSupport A (diameterOrderedEdges A Δ) hEdges (hDiam A Δ hΔ)
  simpa [orderedShellMultiplicity_eq_diameterOrderedEdges_card] using
    le_trans hOrdered (Nat.mul_le_mul_left 2 hSupportCard)

/-- Diameter-specific Conway bound implies the ordinary diameter shell sparsity
component used by the Erdős #132 assembly. -/
theorem diameter_shell_sparse_from_diameter_conway_bound
    (hBound : DiameterConwayThrackleBound) :
    DiameterShellSparseBound := by
  filter_upwards with n
  intro A _hA Δ hΔ
  exact ⟨hΔ.1, hBound A Δ hΔ⟩

/-- Pointwise form of the undirected straight-line thrackle support theorem.
The classical theorem is not asymptotic, so this is the sharper statement that
should eventually be proved or imported. -/
def PointwiseUndirectedThrackleSupportBound : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Endpoint-charging form of the straight-line thrackle theorem.  For each
finite pairwise-intersecting straight-line edge system, it asks for an injective
charge from unordered support edges into the underlying point set.  Once this
map is constructed geometrically, the support bound is only finite
cardinality. -/
def ThrackleEndpointChargingCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
        ∃ charge :
          {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
            Function.Injective charge

/-- Finite cardinal comparison produces an injection.  Mathlib supplies the
opposite direction as `Fintype.card_le_of_injective`; this local lemma gives the
construction needed to convert support-cardinality proofs into endpoint-charge
certificates. -/
theorem exists_injective_of_fintype_card_le
    {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) :
    ∃ f : α → β, Function.Injective f := by
  classical
  let eα := Fintype.equivFin α
  let eβ := Fintype.equivFin β
  let f : α → β := fun a => eβ.symm (Fin.castLE h (eα a))
  refine ⟨f, ?_⟩
  intro a b hab
  apply eα.injective
  have hfin : Fin.castLE h (eα a) = Fin.castLE h (eα b) := by
    apply eβ.symm.injective
    exact hab
  apply Fin.ext
  have hval := congrArg Fin.val hfin
  simpa using hval

/-- A support-cardinality bound is enough to build the endpoint charge. -/
theorem endpoint_charge_of_support_card_le
    {A : Finset Point2} {E : Finset (Point2 × Point2)}
    (hcard : (unorderedEdgeSupport E).card ≤ A.card) :
    ∃ charge :
      {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
        Function.Injective charge := by
  classical
  have hFintype :
      Fintype.card {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} ≤
        Fintype.card {x : Point2 // x ∈ A} := by
    simpa using hcard
  exact exists_injective_of_fintype_card_le hFintype

/-- The pointwise support theorem and the endpoint-charging theorem are
equivalent over finite systems.  This direction packages any cardinal proof as
an explicit charge. -/
theorem thrackle_endpoint_charging_from_pointwise_support
    (h : PointwiseUndirectedThrackleSupportBound) :
    ThrackleEndpointChargingCertificate := by
  intro A E hEdges hNoDisj
  exact endpoint_charge_of_support_card_le (h A E hEdges hNoDisj)

/-- A directed edge set is a star about `v` when every ordered edge has `v` as
one endpoint. -/
def OrderedEdgesIncidentTo (v : Point2) (E : Finset (Point2 × Point2)) : Prop :=
  ∀ e ∈ E, e.1 = v ∨ e.2 = v

/-- Three distinct points in a finite set force cardinality at least three. -/
theorem card_ge_three_of_three_mem_distinct
    {A : Finset Point2} {x y z : Point2}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    3 ≤ A.card := by
  classical
  let T : Finset Point2 := {x, y, z}
  have hsub : T ⊆ A := by
    intro w hw
    simp [T] at hw
    rcases hw with h | h | h
    · exact h ▸ hx
    · exact h ▸ hy
    · exact h ▸ hz
  have hT : T.card = 3 := by
    simp [T, hxy, hxz, hyz]
  exact hT ▸ Finset.card_le_card hsub

/-- On at most two ambient points, every nonloop ordered edge system is a star.
The empty system is a star about `0`; a nonempty system is a star about the
first endpoint of any one edge. -/
theorem exists_incident_vertex_of_card_le_two
    {A : Finset Point2} {E : Finset (Point2 × Point2)}
    (hAcard : A.card ≤ 2)
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) :
    ∃ v : Point2, OrderedEdgesIncidentTo v E := by
  classical
  by_cases hE : E.Nonempty
  · rcases hE with ⟨e0, he0E⟩
    refine ⟨e0.1, ?_⟩
    intro e heE
    by_contra hnot
    have hn1 : e.1 ≠ e0.1 := by
      intro h
      exact hnot (Or.inl h)
    have hn2 : e.2 ≠ e0.1 := by
      intro h
      exact hnot (Or.inr h)
    have he0Data := hEdges e0 he0E
    have heData := hEdges e heE
    by_cases h_e1_eq_e02 : e.1 = e0.2
    · have hthree : 3 ≤ A.card :=
        card_ge_three_of_three_mem_distinct
          he0Data.1 he0Data.2.1 heData.2.1
          he0Data.2.2 hn2.symm (by
            intro h
            exact heData.2.2 (by
              rw [h_e1_eq_e02, h]))
      omega
    · have hthree : 3 ≤ A.card :=
        card_ge_three_of_three_mem_distinct
          he0Data.1 he0Data.2.1 heData.1
          he0Data.2.2 hn1.symm (by
            intro h
            exact h_e1_eq_e02 h.symm)
      omega
  · refine ⟨0, ?_⟩
    intro e he
    exact False.elim (hE ⟨e, he⟩)

/-- On exactly three ambient points, the unordered nonloop support has at most
three edges.  This closes the first non-star finite boundary case: the triangle
itself is maximal. -/
theorem unordered_support_card_le_of_card_eq_three
    {A : Finset Point2} {E : Finset (Point2 × Point2)}
    (hAcard : A.card = 3)
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) :
    (unorderedEdgeSupport E).card ≤ A.card := by
  classical
  rcases Finset.card_eq_three.mp hAcard with ⟨x, y, z, hxy, hxz, hyz, hAeq⟩
  let T : Finset (Sym2 Point2) :=
    {Sym2.mk (x, y), Sym2.mk (x, z), Sym2.mk (y, z)}
  have hsub : unorderedEdgeSupport E ⊆ T := by
    intro u hu
    unfold unorderedEdgeSupport at hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨e, heE, heu⟩
    have heData := hEdges e heE
    rw [hAeq] at heData
    cases e with
    | mk p q =>
      simp at heData heu
      have hp : p = x ∨ p = y ∨ p = z := by
        simpa using heData.1
      have hq : q = x ∨ q = y ∨ q = z := by
        simpa using heData.2.1
      have hpq : p ≠ q := heData.2.2
      rw [← heu]
      rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
      · subst p; subst q; exact False.elim (hpq rfl)
      · subst p; subst q; simp [T, unorderedEdgeOfOrdered]
      · subst p; subst q; simp [T, unorderedEdgeOfOrdered]
      · subst p; subst q
        have hsym : Sym2.mk (y, x) = Sym2.mk (x, y) :=
          (Sym2.eq_iff).mpr (Or.inr ⟨rfl, rfl⟩)
        simp [T, unorderedEdgeOfOrdered, hsym]
      · subst p; subst q; exact False.elim (hpq rfl)
      · subst p; subst q; simp [T, unorderedEdgeOfOrdered]
      · subst p; subst q
        have hsym : Sym2.mk (z, x) = Sym2.mk (x, z) :=
          (Sym2.eq_iff).mpr (Or.inr ⟨rfl, rfl⟩)
        simp [T, unorderedEdgeOfOrdered, hsym]
      · subst p; subst q
        have hsym : Sym2.mk (z, y) = Sym2.mk (y, z) :=
          (Sym2.eq_iff).mpr (Or.inr ⟨rfl, rfl⟩)
        simp [T, unorderedEdgeOfOrdered, hsym]
      · subst p; subst q; exact False.elim (hpq rfl)
  calc
    (unorderedEdgeSupport E).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ A.card := by
      have hT : T.card ≤ 3 := Finset.card_le_three
      omega


/-- If every unordered support edge is represented as `{v, x}` with `x ∈ A`,
then the support admits an injective endpoint charge into `A`.  This is the
finite extraction step behind the star-case thrackle proof. -/
theorem endpoint_charge_of_support_subset_image
    {A : Finset Point2} {E : Finset (Point2 × Point2)} {v : Point2}
    (hsub :
      unorderedEdgeSupport E ⊆ A.image (fun x : Point2 => Sym2.mk (v, x))) :
    ∃ charge :
      {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
        Function.Injective charge := by
  classical
  let f : Point2 → Sym2 Point2 := fun x => Sym2.mk (v, x)
  have hrep :
      ∀ u : {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E},
        ∃ x : Point2, x ∈ A ∧ f x = u.1 := by
    intro u
    have hu : u.1 ∈ A.image f := hsub u.2
    rw [Finset.mem_image] at hu
    rcases hu with ⟨x, hxA, hxu⟩
    exact ⟨x, hxA, hxu⟩
  let charge :
      {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A} :=
    fun u => ⟨Classical.choose (hrep u), (Classical.choose_spec (hrep u)).1⟩
  refine ⟨charge, ?_⟩
  intro u w huw
  apply Subtype.ext
  have hu_eq : f (charge u).1 = u.1 := (Classical.choose_spec (hrep u)).2
  have hw_eq : f (charge w).1 = w.1 := (Classical.choose_spec (hrep w)).2
  have hval : (charge u).1 = (charge w).1 := by
    exact congrArg Subtype.val huw
  calc
    u.1 = f (charge u).1 := hu_eq.symm
    _ = f (charge w).1 := by rw [hval]
    _ = w.1 := hw_eq

/-- Star-case support bound for the thrackle certificate.  If every edge is
incident to one vertex `v`, the unordered support injects into the ambient
point set by taking the other endpoint. -/
theorem unordered_support_card_le_of_incident_vertex
    {A : Finset Point2} {E : Finset (Point2 × Point2)} {v : Point2}
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2)
    (hIncident : OrderedEdgesIncidentTo v E) :
    (unorderedEdgeSupport E).card ≤ A.card := by
  classical
  let f : Point2 → Sym2 Point2 := fun x => Sym2.mk (v, x)
  have hsub : unorderedEdgeSupport E ⊆ A.image f := by
    intro u hu
    unfold unorderedEdgeSupport at hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨e, heE, heu⟩
    have heData := hEdges e heE
    rcases hIncident e heE with hleft | hright
    · refine Finset.mem_image.mpr ⟨e.2, heData.2.1, ?_⟩
      rw [← heu]
      unfold f unorderedEdgeOfOrdered
      cases e with
      | mk p q =>
        simp at hleft ⊢
        subst p
        exact Or.inl rfl
    · refine Finset.mem_image.mpr ⟨e.1, heData.1, ?_⟩
      rw [← heu]
      unfold f unorderedEdgeOfOrdered
      cases e with
      | mk p q =>
        simp at hright ⊢
        subst q
        exact Or.inr rfl
  calc
    (unorderedEdgeSupport E).card ≤ (A.image f).card := Finset.card_le_card hsub
    _ ≤ A.card := Finset.card_image_le

/-- Large non-star residual form of Conway's straight-line thrackle theorem.
The star systems and the `|A| ≤ 3` ambient cases are already finite
bookkeeping; this is the first genuinely large Conway counting target. -/
def LargeNonStarConwayThrackleSupportBound : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackle E →
      4 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Star systems plus all ambient sets of size at most three are closed, so the
large non-star Conway residual implies the standard Conway support theorem. -/
theorem conway_support_bound_from_large_nonstar
    (hLarge : LargeNonStarConwayThrackleSupportBound) :
    ConwayThrackleSupportBound := by
  intro A E hEdges hConway
  by_cases hA2 : A.card ≤ 2
  · rcases exists_incident_vertex_of_card_le_two hA2 hEdges with ⟨v, hIncident⟩
    exact unordered_support_card_le_of_incident_vertex hEdges hIncident
  · by_cases hA3 : A.card = 3
    · exact unordered_support_card_le_of_card_eq_three hA3 hEdges
    · have hA4 : 4 ≤ A.card := by omega
      by_cases hStar : ∃ v : Point2, OrderedEdgesIncidentTo v E
      · rcases hStar with ⟨v, hIncident⟩
        exact unordered_support_card_le_of_incident_vertex hEdges hIncident
      · exact hLarge A E hEdges hConway hA4 (by
          intro v hIncident
          exact hStar ⟨v, hIncident⟩)

/-- Star-case endpoint charge for the thrackle certificate.  This strengthens
the star support bound by constructing the actual injective charge demanded by
`ThrackleEndpointChargingCertificate`. -/
theorem endpoint_charging_of_incident_vertex
    {A : Finset Point2} {E : Finset (Point2 × Point2)} {v : Point2}
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2)
    (hIncident : OrderedEdgesIncidentTo v E) :
    ∃ charge :
      {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
        Function.Injective charge := by
  classical
  let f : Point2 → Sym2 Point2 := fun x => Sym2.mk (v, x)
  have hsub : unorderedEdgeSupport E ⊆ A.image f := by
    intro u hu
    unfold unorderedEdgeSupport at hu
    rw [Finset.mem_image] at hu
    rcases hu with ⟨e, heE, heu⟩
    have heData := hEdges e heE
    rcases hIncident e heE with hleft | hright
    · refine Finset.mem_image.mpr ⟨e.2, heData.2.1, ?_⟩
      rw [← heu]
      unfold f unorderedEdgeOfOrdered
      cases e with
      | mk p q =>
        simp at hleft ⊢
        subst p
        exact Or.inl rfl
    · refine Finset.mem_image.mpr ⟨e.1, heData.1, ?_⟩
      rw [← heu]
      unfold f unorderedEdgeOfOrdered
      cases e with
      | mk p q =>
        simp at hright ⊢
        subst q
        exact Or.inr rfl
  exact endpoint_charge_of_support_subset_image hsub

/-- Non-star residual form of the straight-line thrackle endpoint-charge
problem.  Star systems are already charged by
`endpoint_charging_of_incident_vertex`; this certificate asks only for the
remaining pairwise-intersecting systems with no common incident vertex. -/
def NonStarThrackleEndpointChargingCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        ∃ charge :
          {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
            Function.Injective charge

/-- Large non-star residual form of the straight-line thrackle endpoint-charge
problem.  The `|A| ≤ 2` cases are already stars, so the remaining non-star
certificate only has to start at three ambient points. -/
def LargeNonStarThrackleEndpointChargingCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      3 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        ∃ charge :
          {u : Sym2 Point2 // u ∈ unorderedEdgeSupport E} → {x : Point2 // x ∈ A},
            Function.Injective charge

/-- Cardinal form of the large non-star thrackle residual.  This is the weakest
finite statement needed on the thrackle side after star systems and `|A| ≤ 2`
systems have been closed. -/
def LargeNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      3 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Four-point-or-larger form of the non-star support residual.  The exact
three-point boundary is already closed by
`unordered_support_card_le_of_card_eq_three`. -/
def FourPointNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      4 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Exact four-vertex non-star boundary certificate for straight-line thrackles.
This is the first genuinely geometric finite case after stars and triangles. -/
def ExactFourPointNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      A.card = 4 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Geometric obstruction form of the exact four-vertex thrackle boundary.  If a
non-star straight-line system on four ambient points has more than four
unordered support edges, then two represented ordered edges are geometrically
disjoint.  This is the finite K4 obstruction left after pure counting closes
the triangle boundary. -/
def ExactFourPointK4ObstructionCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      A.card = 4 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
      A.card < (unorderedEdgeSupport E).card →
        ∃ e ∈ E, ∃ f ∈ E, OrderedEdgesGeometricallyDisjoint e f

/-- Support-level version of the exact four-vertex K4 obstruction.  It asks for
two unordered support edges with geometrically disjoint representatives.  This
is the natural next geometric target because the finite graph bookkeeping can
first find the two unordered candidates, and the segment geometry then supplies
the representatives. -/
def ExactFourPointSupportK4ObstructionCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      A.card = 4 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
      A.card < (unorderedEdgeSupport E).card →
        ∃ u ∈ unorderedEdgeSupport E,
          ∃ v ∈ unorderedEdgeSupport E,
            SupportEdgesHaveDisjointRepresentatives E u v

/-- The support-level K4 obstruction implies the ordered-representative K4
obstruction used by the final assembly. -/
theorem exact_fourpoint_k4_obstruction_from_support_obstruction
    (hSupportK4 : ExactFourPointSupportK4ObstructionCertificate) :
    ExactFourPointK4ObstructionCertificate := by
  intro A E hEdges hAcard hNonStar hgt
  rcases hSupportK4 A E hEdges hAcard hNonStar hgt with
    ⟨u, _hu, v, _hv, hDisjSupport⟩
  exact ordered_disjoint_pair_of_support_disjoint_pair hDisjSupport

/-- The exact K4 obstruction proves the exact four-point support bound under
the pairwise-intersection hypothesis. -/
theorem exact_fourpoint_support_bound_from_k4_obstruction
    (hK4 : ExactFourPointK4ObstructionCertificate) :
    ExactFourPointNonStarThrackleSupportBoundCertificate := by
  intro A E hEdges hNoDisj hAcard hNonStar
  by_contra hnot
  have hgt : A.card < (unorderedEdgeSupport E).card := Nat.lt_of_not_ge hnot
  rcases hK4 A E hEdges hAcard hNonStar hgt with ⟨e, he, f, hf, hDisj⟩
  exact hNoDisj e he f hf hDisj

/-! ### Plücker-based 4-point orientation dichotomy

The Plücker identity (`orient2_alternating_sum_eq_zero`) plus a sum-of-squares
argument forces a sign pattern among the four triangle orientations of any four
points.  This is the algebraic heart of the K4 obstruction: it routes every
non-degenerate 4-point configuration into at least one matching whose two
segments lie on the same strict side of a common line, which by
`same_side_segments_disjoint` makes them geometrically disjoint.

The lemma is stated purely on four reals so it can be reused independently of
the geometric instantiation; the four reals will later be set to the four
`orient2`-values among `{a,b,c,d}`. -/

/-- Sum-of-squares dichotomy.  Given four reals satisfying the Plücker linear
relation `o₁ - o₂ + o₃ - o₄ = 0`, if all six bilinear sign witnesses
`o₃·o₄, o₁·o₂, -o₂·o₄, -o₁·o₃, o₂·o₃, o₁·o₄` are nonpositive, then all four
reals vanish.

Proof: from `o₁ + o₃ = o₂ + o₄` we get
`(o₁+o₃)² = (o₁+o₃)(o₂+o₄) = o₁o₂ + o₁o₄ + o₂o₃ + o₃o₄ ≤ 0`,
so `o₁ + o₃ = 0`, hence `o₃ = -o₁` and `o₁o₃ = -o₁² ≤ 0`; combined with the
hypothesis `o₁o₃ ≥ 0` we get `o₁ = 0`, then `o₃ = 0`, and the symmetric step
gives `o₂ = o₄ = 0`. -/
theorem four_reals_orientation_dichotomy_alg
    {o₁ o₂ o₃ o₄ : ℝ}
    (hPluck : o₁ - o₂ + o₃ - o₄ = 0)
    (h₃₄ : o₃ * o₄ ≤ 0) (h₁₂ : o₁ * o₂ ≤ 0)
    (h₂₄ : 0 ≤ o₂ * o₄) (h₁₃ : 0 ≤ o₁ * o₃)
    (h₂₃ : o₂ * o₃ ≤ 0) (h₁₄ : o₁ * o₄ ≤ 0) :
    o₁ = 0 ∧ o₂ = 0 ∧ o₃ = 0 ∧ o₄ = 0 := by
  have hP : o₁ + o₃ = o₂ + o₄ := by linarith
  have hExpand : (o₁ + o₃) * (o₂ + o₄) ≤ 0 := by nlinarith
  have hSqLe : (o₁ + o₃) ^ 2 ≤ 0 := by
    have hRewrite : (o₁ + o₃) ^ 2 = (o₁ + o₃) * (o₂ + o₄) := by
      have : (o₁ + o₃) ^ 2 = (o₁ + o₃) * (o₁ + o₃) := by ring
      rw [this, hP]
    rw [hRewrite]; exact hExpand
  have hSqEq : (o₁ + o₃) ^ 2 = 0 :=
    le_antisymm hSqLe (sq_nonneg _)
  have hSum₁₃ : o₁ + o₃ = 0 := by
    have := sq_eq_zero_iff.mp hSqEq
    exact this
  have hSum₂₄ : o₂ + o₄ = 0 := by linarith
  have hO₃_eq : o₃ = -o₁ := by linarith
  have h_o1sq_le : o₁ ^ 2 ≤ 0 := by
    have hProd : o₁ * o₃ = -(o₁ ^ 2) := by
      rw [hO₃_eq]; ring
    linarith [h₁₃]
  have h_o1sq_eq : o₁ ^ 2 = 0 := le_antisymm h_o1sq_le (sq_nonneg _)
  have hO₁ : o₁ = 0 := sq_eq_zero_iff.mp h_o1sq_eq
  have hO₃ : o₃ = 0 := by linarith
  have hO₄_eq : o₄ = -o₂ := by linarith
  have h_o2sq_le : o₂ ^ 2 ≤ 0 := by
    have hProd : o₂ * o₄ = -(o₂ ^ 2) := by
      rw [hO₄_eq]; ring
    linarith [h₂₄]
  have h_o2sq_eq : o₂ ^ 2 = 0 := le_antisymm h_o2sq_le (sq_nonneg _)
  have hO₂ : o₂ = 0 := sq_eq_zero_iff.mp h_o2sq_eq
  have hO₄ : o₄ = 0 := by linarith
  exact ⟨hO₁, hO₂, hO₃, hO₄⟩

/-- Geometric Plücker dichotomy for four points.  If at least one of the four
triangle orientations among `{a,b,c,d}` is nonzero, then at least one of the
six same-side disjointness witnesses for the three perfect matchings of `K₄`
holds.  Each witness, via `same_side_segments_disjoint`, certifies one
matching as geometrically disjoint.

The six disjuncts are exactly the `0 < orient2 X Y P * orient2 X Y Q` hypotheses
of `same_side_segments_disjoint` for the lines and remaining points of the
three matchings `M₁ = {ab,cd}`, `M₂ = {ac,bd}`, `M₃ = {ad,bc}`. -/
theorem four_points_orientation_dichotomy
    (a b c d : Point2)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    0 < orient2 a b c * orient2 a b d ∨
    0 < orient2 c d a * orient2 c d b ∨
    0 < orient2 a c b * orient2 a c d ∨
    0 < orient2 b d a * orient2 b d c ∨
    0 < orient2 a d b * orient2 a d c ∨
    0 < orient2 b c a * orient2 b c d := by
  -- Substitute the four `orient2` values as o₁, o₂, o₃, o₄.
  set o₁ := orient2 b c d with ho₁_def
  set o₂ := orient2 a c d with ho₂_def
  set o₃ := orient2 a b d with ho₃_def
  set o₄ := orient2 a b c with ho₄_def
  -- Plücker linear relation.
  have hPluck : o₁ - o₂ + o₃ - o₄ = 0 := by
    have h := orient2_alternating_sum_eq_zero a b c d
    linarith
  -- `orient2` swap/cyclic identities used below.
  have hcd_a : orient2 c d a = o₂ := by
    show orient2 c d a = orient2 a c d
    rw [orient2_cyclic, orient2_cyclic]
  have hcd_b : orient2 c d b = o₁ := by
    show orient2 c d b = orient2 b c d
    rw [orient2_cyclic, orient2_cyclic]
  have hacb : orient2 a c b = -o₄ := orient2_swap₂₃ a b c
  have hbda : orient2 b d a = o₃ := by
    show orient2 b d a = orient2 a b d
    rw [orient2_cyclic, orient2_cyclic]
  have hbdc : orient2 b d c = -o₁ := by
    have := orient2_swap₂₃ b c d
    -- orient2_swap₂₃ : orient2 b d c = - orient2 b c d
    linarith
  have hadb : orient2 a d b = -o₃ := orient2_swap₂₃ a b d
  have hadc : orient2 a d c = -o₂ := orient2_swap₂₃ a c d
  have hbca : orient2 b c a = o₄ := by
    show orient2 b c a = orient2 a b c
    rw [orient2_cyclic, orient2_cyclic]
  by_contra hAll
  push_neg at hAll
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hAll
  -- Translate each negated witness into a sign condition on o₁, o₂, o₃, o₄.
  have h₃₄ : o₃ * o₄ ≤ 0 := by
    have h : o₄ * o₃ ≤ 0 := h1
    linarith [h, (by ring : o₃ * o₄ = o₄ * o₃)]
  have h₁₂ : o₁ * o₂ ≤ 0 := by
    rw [hcd_a, hcd_b] at h2
    linarith [h2, (by ring : o₁ * o₂ = o₂ * o₁)]
  -- h3 : (-o₄) * o₂ ≤ 0  ⇒  o₂ * o₄ ≥ 0.
  have h₂₄ : 0 ≤ o₂ * o₄ := by
    rw [hacb] at h3
    nlinarith [h3]
  -- h4 : o₃ * (-o₁) ≤ 0  ⇒  o₁ * o₃ ≥ 0.
  have h₁₃ : 0 ≤ o₁ * o₃ := by
    rw [hbda, hbdc] at h4
    nlinarith [h4]
  -- h5 : (-o₃)(-o₂) ≤ 0  ⇒  o₂ * o₃ ≤ 0.
  have h₂₃ : o₂ * o₃ ≤ 0 := by
    rw [hadb, hadc] at h5
    nlinarith [h5]
  -- h6 : o₄ * o₁ ≤ 0  ⇒  o₁ * o₄ ≤ 0.
  have h₁₄ : o₁ * o₄ ≤ 0 := by
    rw [hbca] at h6
    linarith [h6, (by ring : o₁ * o₄ = o₄ * o₁)]
  -- Apply the algebraic dichotomy.
  obtain ⟨hO₁, hO₂, hO₃, hO₄⟩ :=
    four_reals_orientation_dichotomy_alg hPluck h₃₄ h₁₂ h₂₄ h₁₃ h₂₃ h₁₄
  -- All four orientations vanish, contradicting `hNotAllCollinear`.
  rcases hNotAllCollinear with h | h | h | h
  · exact h hO₄
  · exact h hO₃
  · exact h hO₂
  · exact h hO₁

/-- Symmetry of `OrderedEdgesGeometricallyDisjoint`.  Two ordered edges are
geometrically disjoint regardless of which one is the first argument. -/
theorem ordered_edges_geometrically_disjoint_symm
    {e f : Point2 × Point2}
    (h : OrderedEdgesGeometricallyDisjoint e f) :
    OrderedEdgesGeometricallyDisjoint f e := by
  intro hmeet
  exact h (ordered_edges_meet_symm hmeet)

/-- Geometric four-point matching dichotomy (noncollinear case).  For any four
points `a, b, c, d` that are not all collinear (some `orient2` among triples
is nonzero), at least one of the three perfect matchings of `K₄` consists of
two geometrically disjoint segments.  This is the heart of the Conway-K4
obstruction: it routes every non-degenerate 4-point configuration into a
disjoint matching using only `same_side_segments_disjoint` and the Plücker
orientation identity. -/
theorem four_distinct_points_one_matching_disjoint_noncollinear
    (a b c d : Point2)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d) ∨
    OrderedEdgesGeometricallyDisjoint (a, c) (b, d) ∨
    OrderedEdgesGeometricallyDisjoint (a, d) (b, c) := by
  rcases four_points_orientation_dichotomy a b c d hNotAllCollinear with
    h | h | h | h | h | h
  · exact Or.inl (same_side_segments_disjoint h)
  · refine Or.inl ?_
    exact ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint h)
  · exact Or.inr (Or.inl (same_side_segments_disjoint h))
  · refine Or.inr (Or.inl ?_)
    exact ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint h)
  · exact Or.inr (Or.inr (same_side_segments_disjoint h))
  · refine Or.inr (Or.inr ?_)
    exact ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint h)

/-! ### Conway-conditioned 4-point K4 obstruction

The existing `ExactFourPointK4ObstructionCertificate` (above) asks for a
geometrically disjoint pair under the weak hypothesis "every pair of ordered
edges meets" (i.e., `¬ OrderedEdgesGeometricallyDisjoint`).  That hypothesis
is too weak: with four collinear points, a five-edge non-star configuration
exists where every pair meets (some pairs overlap on a common sub-segment)
yet no disjoint pair can be extracted.  The corresponding "intersecting
support bound" certificate `ExactFourPointNonStarThrackleSupportBoundCertificate`
is therefore false in general.

Conway's actual theorem uses the *simple-meeting* condition
`OrderedEdgesMeetSimply` (exactly one common point), which excludes the
overlapping collinear pathology.  Below we state and (mostly) discharge the
correct Conway-conditioned K4 obstruction: under simple-meeting, four ambient
points cannot host more than four unordered support edges.  The noncollinear
case is closed by `four_distinct_points_one_matching_disjoint_noncollinear`;
the all-collinear case is the only remaining hand geometry (sorting on a
line). -/

/-- Conway-conditioned exact four-point support bound.  This is the correct
shape of the K4 boundary: a Conway thrackle on four points with no incident
vertex has at most four unordered support edges. -/
def ExactFourPointConwayThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackle E →
      A.card = 4 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- All-collinear residual for the Conway K4 obstruction.  If four distinct
collinear points host a Conway thrackle with no incident vertex, the unordered
support is bounded by 4.  This is the only remaining hand geometry: in the
collinear case the algebraic dichotomy degenerates and we must sort by line
parameter.  Stated separately so the noncollinear case can close immediately. -/
def CollinearFourPointConwayResidual : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      IsConwayThrackle E →
      A.card = 4 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
      (∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, orient2 p q r = 0) →
        (unorderedEdgeSupport E).card ≤ A.card

/-! ### Pairwise strong dichotomy (algebraic + geometric)

Three lemmas, one per pair `(M_i, M_j)` of matchings.  If both matchings have
all their same-side disjointness witnesses fail (i.e., neither is "disjoint via
same-side"), then the SOS-Plücker argument forces a pair of zero `orient2`
values whose triples share two points; combined with the distinctness of the
four ambient points this forces all four points to be collinear. -/

/-- Sum-of-squares pair lemma.  For four reals satisfying Plücker and the four
sign-product conditions `o₃·o₄ ≤ 0`, `o₁·o₂ ≤ 0`, `o₂·o₃ ≤ 0`, `o₁·o₄ ≤ 0`
(the joint failure of the `M₁`/`M₃` same-side witnesses), the SOS expansion of
`(o₁+o₃)(o₂+o₄)` is nonpositive while equalling `(o₁+o₃)² ≥ 0`, so
`o₁ + o₃ = 0 = o₂ + o₄`, and one of `o₁·o₂ = 0` follows from the resulting
algebra. -/
theorem four_reals_M1_M3_pair_sos
    {o₁ o₂ o₃ o₄ : ℝ}
    (hPluck : o₁ - o₂ + o₃ - o₄ = 0)
    (h₃₄ : o₃ * o₄ ≤ 0) (h₁₂ : o₁ * o₂ ≤ 0)
    (h₂₃ : o₂ * o₃ ≤ 0) (h₁₄ : o₁ * o₄ ≤ 0) :
    (o₁ = 0 ∧ o₃ = 0) ∨ (o₂ = 0 ∧ o₄ = 0) := by
  have hP : o₁ + o₃ = o₂ + o₄ := by linarith
  have hExpand : (o₁ + o₃) * (o₂ + o₄) ≤ 0 := by nlinarith
  have hSqLe : (o₁ + o₃) ^ 2 ≤ 0 := by
    have hRewrite : (o₁ + o₃) ^ 2 = (o₁ + o₃) * (o₂ + o₄) := by
      have : (o₁ + o₃) ^ 2 = (o₁ + o₃) * (o₁ + o₃) := by ring
      rw [this, hP]
    rw [hRewrite]; exact hExpand
  have hSqEq : (o₁ + o₃) ^ 2 = 0 := le_antisymm hSqLe (sq_nonneg _)
  have hSum₁₃ : o₁ + o₃ = 0 := sq_eq_zero_iff.mp hSqEq
  have hSum₂₄ : o₂ + o₄ = 0 := by linarith
  have hO₃_eq : o₃ = -o₁ := by linarith
  have hO₄_eq : o₄ = -o₂ := by linarith
  -- o₂ * o₃ ≤ 0 with o₃ = -o₁ gives -o₁o₂ ≤ 0 i.e. o₁o₂ ≥ 0.  Combined with h₁₂.
  have h_o₁o₂_zero : o₁ * o₂ = 0 := by
    have h1 : 0 ≤ o₁ * o₂ := by
      have hRw : o₂ * o₃ = -(o₁ * o₂) := by rw [hO₃_eq]; ring
      linarith [h₂₃, hRw]
    linarith [h₁₂]
  rcases mul_eq_zero.mp h_o₁o₂_zero with hO₁ | hO₂
  · left
    refine ⟨hO₁, ?_⟩
    rw [hO₃_eq, hO₁]; ring
  · right
    refine ⟨hO₂, ?_⟩
    rw [hO₄_eq, hO₂]; ring

/-- Geometric two-zero collinearity.  If `orient2 a b d = 0` and
`orient2 b c d = 0` with `b ≠ d`, then all four points `a, b, c, d` are
collinear: lines `bd` (from the first zero) and `bd` (from the second zero)
are the same line through `b, d`, and both `a` and `c` lie on it.  The
conclusion is recorded as `orient2 a b c = 0` (since `a, b, c` collinear). -/
theorem orient2_zero_two_zeros_share_bd
    {a b c d : Point2} (hbd : b ≠ d)
    (h₃ : orient2 a b d = 0) (h₁ : orient2 b c d = 0) :
    orient2 a b c = 0 := by
  -- From `h₁ : orient2 b c d = 0` rewrite as `orient2 b d c = 0` via swap.
  have h_bd_c : orient2 b d c = 0 := by
    have hsw : orient2 b d c = -orient2 b c d := orient2_swap₂₃ b c d
    linarith
  -- Reorder `h₃` to use `b, d` as the "fixed line": `orient2 b d a = 0`.
  have h_bd_a : orient2 b d a = 0 := by
    have hc : orient2 a b d = orient2 b d a := orient2_cyclic a b d
    linarith
  -- Apply `orient2_zero_transitive` with `a := b`, `b := d`, `c := a`, `d := c`.
  have h_b_a_c : orient2 b a c = 0 :=
    orient2_zero_transitive hbd h_bd_a h_bd_c
  -- Convert to `orient2 a b c = 0` via swap.
  have hsw : orient2 b a c = -orient2 a b c := orient2_swap₁₂ a b c
  linarith

/-- Pair `(M₁, M₂)`: both fail their same-side disjointness witnesses ⇒
either `o₁ = o₄ = 0` (collinearity of `{a,b,c}` and `{b,c,d}`, sharing `b, c`)
or `o₂ = o₃ = 0` (collinearity of `{a,c,d}` and `{a,b,d}`, sharing `a, d`).
Uses `(o₁ - o₄)(o₂ - o₃)` whose sign is forced to zero by Plücker
`o₁ - o₄ = o₂ - o₃` and the four sign hypotheses. -/
theorem four_reals_M1_M2_pair_sos
    {o₁ o₂ o₃ o₄ : ℝ}
    (hPluck : o₁ - o₂ + o₃ - o₄ = 0)
    (h₃₄ : o₃ * o₄ ≤ 0) (h₁₂ : o₁ * o₂ ≤ 0)   -- M₁ fail
    (h₂₄ : 0 ≤ o₂ * o₄) (h₁₃ : 0 ≤ o₁ * o₃) : -- M₂ fail
    (o₁ = 0 ∧ o₄ = 0) ∨ (o₂ = 0 ∧ o₃ = 0) := by
  have hP : o₁ - o₄ = o₂ - o₃ := by linarith
  have hExpand : (o₁ - o₄) * (o₂ - o₃) ≤ 0 := by nlinarith
  have hSqLe : (o₁ - o₄) ^ 2 ≤ 0 := by
    have hRewrite : (o₁ - o₄) ^ 2 = (o₁ - o₄) * (o₂ - o₃) := by
      have : (o₁ - o₄) ^ 2 = (o₁ - o₄) * (o₁ - o₄) := by ring
      rw [this, hP]
    rw [hRewrite]; exact hExpand
  have hSqEq : (o₁ - o₄) ^ 2 = 0 := le_antisymm hSqLe (sq_nonneg _)
  have hDiff₁₄ : o₁ - o₄ = 0 := sq_eq_zero_iff.mp hSqEq
  have hO₄_eq : o₄ = o₁ := by linarith
  have hO₃_eq : o₃ = o₂ := by linarith
  -- o₂ * o₄ = o₁ * o₂, combine with h₁₂ : o₁ * o₂ ≤ 0 and h₂₄ : 0 ≤ o₂ * o₄.
  have h_o₁o₂_zero : o₁ * o₂ = 0 := by
    have hRw : o₂ * o₄ = o₁ * o₂ := by rw [hO₄_eq]; ring
    linarith [h₁₂, h₂₄, hRw]
  rcases mul_eq_zero.mp h_o₁o₂_zero with hO₁ | hO₂
  · left
    refine ⟨hO₁, ?_⟩
    linarith
  · right
    refine ⟨hO₂, ?_⟩
    linarith

/-- Pair `(M₂, M₃)`: both fail their same-side disjointness witnesses ⇒
either `o₁ = o₂ = 0` (collinearity of `{b,c,d}` and `{a,c,d}`, sharing `c, d`)
or `o₃ = o₄ = 0` (collinearity of `{a,b,d}` and `{a,b,c}`, sharing `a, b`).
Uses `(o₁ - o₂)(o₃ - o₄) = -(o₁ - o₂)²` (after Plücker) plus the four sign
hypotheses. -/
theorem four_reals_M2_M3_pair_sos
    {o₁ o₂ o₃ o₄ : ℝ}
    (hPluck : o₁ - o₂ + o₃ - o₄ = 0)
    (h₂₄ : 0 ≤ o₂ * o₄) (h₁₃ : 0 ≤ o₁ * o₃)   -- M₂ fail
    (h₂₃ : o₂ * o₃ ≤ 0) (h₁₄ : o₁ * o₄ ≤ 0) : -- M₃ fail
    (o₁ = 0 ∧ o₂ = 0) ∨ (o₃ = 0 ∧ o₄ = 0) := by
  have hP : o₁ - o₂ = -(o₃ - o₄) := by linarith
  have hExpand : 0 ≤ (o₁ - o₂) * (o₃ - o₄) := by nlinarith
  have hSqNeg : (o₁ - o₂) * (o₃ - o₄) = -(o₃ - o₄) ^ 2 := by
    have : (o₁ - o₂) * (o₃ - o₄) = -(o₃ - o₄) * (o₃ - o₄) := by
      rw [show o₁ - o₂ = -(o₃ - o₄) from hP]
    rw [this]; ring
  have hSqEq : (o₃ - o₄) ^ 2 = 0 := by
    have hSqLe : (o₃ - o₄) ^ 2 ≤ 0 := by
      have : -(o₃ - o₄) ^ 2 ≥ 0 := by linarith [hExpand, hSqNeg]
      linarith
    exact le_antisymm hSqLe (sq_nonneg _)
  have hDiff₃₄ : o₃ - o₄ = 0 := sq_eq_zero_iff.mp hSqEq
  have hO₄_eq : o₄ = o₃ := by linarith
  have hO₂_eq : o₂ = o₁ := by linarith
  -- o₂ * o₃ = o₁ * o₃, combine with h₂₃ ≤ 0 and h₁₃ ≥ 0.
  have h_o₁o₃_zero : o₁ * o₃ = 0 := by
    have hRw : o₂ * o₃ = o₁ * o₃ := by rw [hO₂_eq]
    linarith [h₂₃, h₁₃, hRw]
  rcases mul_eq_zero.mp h_o₁o₃_zero with hO₁ | hO₃
  · left
    refine ⟨hO₁, ?_⟩
    linarith
  · right
    refine ⟨hO₃, ?_⟩
    linarith

/-! ### Geometric "all four collinear" closure from any shared pair of zeros

For each of the six possible shared vertex pairs `{p, q} ⊂ {a, b, c, d}`, two
zero orientations whose underlying triples both contain `{p, q}` together
with `p ≠ q` force the remaining `orient2` values among `{a, b, c, d}` to
vanish, by `orient2_zero_transitive` plus the Plücker identity. -/

/-- `o₁ = o₃ = 0` shared at `b, d` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o1_o3_zero
    {a b c d : Point2} (hbd : b ≠ d)
    (h₁ : orient2 b c d = 0) (h₃ : orient2 a b d = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  have h₄ : orient2 a b c = 0 :=
    orient2_zero_two_zeros_share_bd hbd h₃ h₁
  have h₂ : orient2 a c d = 0 := by
    -- Plücker: o₁ - o₂ + o₃ - o₄ = 0 ⇒ o₂ = o₁ + o₃ - o₄ = 0.
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h₄, h₃, h₂, h₁⟩

/-- `o₂ = o₄ = 0` shared at `a, c` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o2_o4_zero
    {a b c d : Point2} (hac : a ≠ c)
    (h₂ : orient2 a c d = 0) (h₄ : orient2 a b c = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  -- Derive orient2 a b d = 0 using transitivity through line ac.
  have h_ac_b : orient2 a c b = 0 := by
    have := orient2_swap₂₃ a b c
    -- orient2 a c b = -orient2 a b c
    linarith
  have h_a_b_d : orient2 a b d = 0 := by
    -- Apply orient2_zero_transitive with line ac: get orient2 a b d.
    -- orient2_zero_transitive hac h_ac_b h₂ : orient2 a b d = 0.
    exact orient2_zero_transitive hac h_ac_b h₂
  have h_o1 : orient2 b c d = 0 := by
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h₄, h_a_b_d, h₂, h_o1⟩

/-- `o₁ = o₄ = 0` shared at `b, c` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o1_o4_zero
    {a b c d : Point2} (hbc : b ≠ c)
    (h₁ : orient2 b c d = 0) (h₄ : orient2 a b c = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  -- Apply orient2_zero_transitive with line bc.
  have h_bc_a : orient2 b c a = 0 := by
    have hcy : orient2 a b c = orient2 b c a := orient2_cyclic a b c
    linarith
  have h_b_a_d : orient2 b a d = 0 :=
    orient2_zero_transitive hbc h_bc_a h₁
  have h_a_b_d : orient2 a b d = 0 := by
    have := orient2_swap₁₂ a b d
    linarith
  have h_o2 : orient2 a c d = 0 := by
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h₄, h_a_b_d, h_o2, h₁⟩

/-- `o₂ = o₃ = 0` shared at `a, d` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o2_o3_zero
    {a b c d : Point2} (had : a ≠ d)
    (h₂ : orient2 a c d = 0) (h₃ : orient2 a b d = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  -- Apply orient2_zero_transitive with line ad.
  have h_ad_c : orient2 a d c = 0 := by
    have := orient2_swap₂₃ a c d
    linarith
  have h_ad_b : orient2 a d b = 0 := by
    have := orient2_swap₂₃ a b d
    linarith
  have h_a_c_b : orient2 a c b = 0 :=
    orient2_zero_transitive had h_ad_c h_ad_b
  have h_a_b_c : orient2 a b c = 0 := by
    have := orient2_swap₂₃ a b c
    linarith
  have h_o1 : orient2 b c d = 0 := by
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h_a_b_c, h₃, h₂, h_o1⟩

/-- `o₁ = o₂ = 0` shared at `c, d` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o1_o2_zero
    {a b c d : Point2} (hcd : c ≠ d)
    (h₁ : orient2 b c d = 0) (h₂ : orient2 a c d = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  -- Apply orient2_zero_transitive with line cd.
  have h_cd_a : orient2 c d a = 0 := by
    have hcy : orient2 a c d = orient2 c d a := by
      rw [orient2_cyclic, orient2_cyclic]
    linarith
  have h_cd_b : orient2 c d b = 0 := by
    have hcy : orient2 b c d = orient2 c d b := by
      rw [orient2_cyclic, orient2_cyclic]
    linarith
  have h_c_a_b : orient2 c a b = 0 :=
    orient2_zero_transitive hcd h_cd_a h_cd_b
  have h_a_b_c : orient2 a b c = 0 := by
    have hcy : orient2 c a b = orient2 a b c := by
      rw [orient2_cyclic, orient2_cyclic]
    linarith
  have h_o3 : orient2 a b d = 0 := by
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h_a_b_c, h_o3, h₂, h₁⟩

/-- `o₃ = o₄ = 0` shared at `a, b` ⇒ all four orientations vanish. -/
theorem orient2_all_zero_of_o3_o4_zero
    {a b c d : Point2} (hab : a ≠ b)
    (h₃ : orient2 a b d = 0) (h₄ : orient2 a b c = 0) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  have h_o2 : orient2 a c d = 0 :=
    orient2_zero_transitive hab h₄ h₃
  have h_o1 : orient2 b c d = 0 := by
    have hPl := orient2_alternating_sum_eq_zero a b c d
    linarith
  exact ⟨h₄, h₃, h_o2, h_o1⟩

/-! ### Pair-fail geometric closures (the three combined lemmas)

Each "pair-fail" lemma combines an algebraic pair-SOS lemma with the
appropriate geometric `orient2_all_zero_of_*` closure to conclude that two
matchings failing all their same-side witnesses forces every triple of the
four ambient points to be collinear. -/

/-- Pair `(M₁, M₃)`: if all four same-side witnesses fail (`M₁`'s two and
`M₃`'s two), all four `orient2` values among `{a, b, c, d}` vanish. -/
theorem orient2_M1_M3_pair_fail_all_collinear
    {a b c d : Point2}
    (hbd : b ≠ d) (hac : a ≠ c)
    (h_M1a : ¬ (0 < orient2 a b c * orient2 a b d))
    (h_M1b : ¬ (0 < orient2 c d a * orient2 c d b))
    (h_M3a : ¬ (0 < orient2 a d b * orient2 a d c))
    (h_M3b : ¬ (0 < orient2 b c a * orient2 b c d)) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  set o₁ := orient2 b c d with ho₁
  set o₂ := orient2 a c d with ho₂
  set o₃ := orient2 a b d with ho₃
  set o₄ := orient2 a b c with ho₄
  have hPluck : o₁ - o₂ + o₃ - o₄ = 0 := by
    have h := orient2_alternating_sum_eq_zero a b c d
    linarith
  have hcd_a : orient2 c d a = o₂ := by
    show orient2 c d a = orient2 a c d
    rw [orient2_cyclic, orient2_cyclic]
  have hcd_b : orient2 c d b = o₁ := by
    show orient2 c d b = orient2 b c d
    rw [orient2_cyclic, orient2_cyclic]
  have hadb : orient2 a d b = -o₃ := orient2_swap₂₃ a b d
  have hadc : orient2 a d c = -o₂ := orient2_swap₂₃ a c d
  have hbca : orient2 b c a = o₄ := by
    show orient2 b c a = orient2 a b c
    rw [orient2_cyclic, orient2_cyclic]
  have h₃₄ : o₃ * o₄ ≤ 0 := by
    have h : o₄ * o₃ ≤ 0 := not_lt.mp h_M1a
    linarith [(by ring : o₃ * o₄ = o₄ * o₃)]
  have h₁₂ : o₁ * o₂ ≤ 0 := by
    rw [hcd_a, hcd_b] at h_M1b
    have h := not_lt.mp h_M1b
    linarith [h, (by ring : o₁ * o₂ = o₂ * o₁)]
  have h₂₃ : o₂ * o₃ ≤ 0 := by
    rw [hadb, hadc] at h_M3a
    have h := not_lt.mp h_M3a
    nlinarith [h]
  have h₁₄ : o₁ * o₄ ≤ 0 := by
    rw [hbca] at h_M3b
    have h := not_lt.mp h_M3b
    linarith [h, (by ring : o₁ * o₄ = o₄ * o₁)]
  rcases four_reals_M1_M3_pair_sos hPluck h₃₄ h₁₂ h₂₃ h₁₄ with
    ⟨hO₁, hO₃⟩ | ⟨hO₂, hO₄⟩
  · exact orient2_all_zero_of_o1_o3_zero hbd hO₁ hO₃
  · exact orient2_all_zero_of_o2_o4_zero hac hO₂ hO₄

/-- Pair `(M₁, M₂)`: if all four same-side witnesses fail, all `orient2`
values vanish. -/
theorem orient2_M1_M2_pair_fail_all_collinear
    {a b c d : Point2}
    (hbc : b ≠ c) (had : a ≠ d)
    (h_M1a : ¬ (0 < orient2 a b c * orient2 a b d))
    (h_M1b : ¬ (0 < orient2 c d a * orient2 c d b))
    (h_M2a : ¬ (0 < orient2 a c b * orient2 a c d))
    (h_M2b : ¬ (0 < orient2 b d a * orient2 b d c)) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  set o₁ := orient2 b c d with ho₁
  set o₂ := orient2 a c d with ho₂
  set o₃ := orient2 a b d with ho₃
  set o₄ := orient2 a b c with ho₄
  have hPluck : o₁ - o₂ + o₃ - o₄ = 0 := by
    have h := orient2_alternating_sum_eq_zero a b c d
    linarith
  have hcd_a : orient2 c d a = o₂ := by
    show orient2 c d a = orient2 a c d
    rw [orient2_cyclic, orient2_cyclic]
  have hcd_b : orient2 c d b = o₁ := by
    show orient2 c d b = orient2 b c d
    rw [orient2_cyclic, orient2_cyclic]
  have hacb : orient2 a c b = -o₄ := orient2_swap₂₃ a b c
  have hbda : orient2 b d a = o₃ := by
    show orient2 b d a = orient2 a b d
    rw [orient2_cyclic, orient2_cyclic]
  have hbdc : orient2 b d c = -o₁ := by
    have hsw : orient2 b d c = -orient2 b c d := orient2_swap₂₃ b c d
    linarith
  have h₃₄ : o₃ * o₄ ≤ 0 := by
    have h : o₄ * o₃ ≤ 0 := not_lt.mp h_M1a
    linarith [(by ring : o₃ * o₄ = o₄ * o₃)]
  have h₁₂ : o₁ * o₂ ≤ 0 := by
    rw [hcd_a, hcd_b] at h_M1b
    have h := not_lt.mp h_M1b
    linarith [h, (by ring : o₁ * o₂ = o₂ * o₁)]
  have h₂₄ : 0 ≤ o₂ * o₄ := by
    rw [hacb] at h_M2a
    have h := not_lt.mp h_M2a
    nlinarith [h]
  have h₁₃ : 0 ≤ o₁ * o₃ := by
    rw [hbda, hbdc] at h_M2b
    have h := not_lt.mp h_M2b
    nlinarith [h]
  rcases four_reals_M1_M2_pair_sos hPluck h₃₄ h₁₂ h₂₄ h₁₃ with
    ⟨hO₁, hO₄⟩ | ⟨hO₂, hO₃⟩
  · exact orient2_all_zero_of_o1_o4_zero hbc hO₁ hO₄
  · exact orient2_all_zero_of_o2_o3_zero had hO₂ hO₃

/-- Pair `(M₂, M₃)`: if all four same-side witnesses fail, all `orient2`
values vanish. -/
theorem orient2_M2_M3_pair_fail_all_collinear
    {a b c d : Point2}
    (hcd : c ≠ d) (hab : a ≠ b)
    (h_M2a : ¬ (0 < orient2 a c b * orient2 a c d))
    (h_M2b : ¬ (0 < orient2 b d a * orient2 b d c))
    (h_M3a : ¬ (0 < orient2 a d b * orient2 a d c))
    (h_M3b : ¬ (0 < orient2 b c a * orient2 b c d)) :
    orient2 a b c = 0 ∧ orient2 a b d = 0 ∧
      orient2 a c d = 0 ∧ orient2 b c d = 0 := by
  set o₁ := orient2 b c d with ho₁
  set o₂ := orient2 a c d with ho₂
  set o₃ := orient2 a b d with ho₃
  set o₄ := orient2 a b c with ho₄
  have hPluck : o₁ - o₂ + o₃ - o₄ = 0 := by
    have h := orient2_alternating_sum_eq_zero a b c d
    linarith
  have hacb : orient2 a c b = -o₄ := orient2_swap₂₃ a b c
  have hbda : orient2 b d a = o₃ := by
    show orient2 b d a = orient2 a b d
    rw [orient2_cyclic, orient2_cyclic]
  have hbdc : orient2 b d c = -o₁ := by
    have hsw : orient2 b d c = -orient2 b c d := orient2_swap₂₃ b c d
    linarith
  have hadb : orient2 a d b = -o₃ := orient2_swap₂₃ a b d
  have hadc : orient2 a d c = -o₂ := orient2_swap₂₃ a c d
  have hbca : orient2 b c a = o₄ := by
    show orient2 b c a = orient2 a b c
    rw [orient2_cyclic, orient2_cyclic]
  have h₂₄ : 0 ≤ o₂ * o₄ := by
    rw [hacb] at h_M2a
    have h := not_lt.mp h_M2a
    nlinarith [h]
  have h₁₃ : 0 ≤ o₁ * o₃ := by
    rw [hbda, hbdc] at h_M2b
    have h := not_lt.mp h_M2b
    nlinarith [h]
  have h₂₃ : o₂ * o₃ ≤ 0 := by
    rw [hadb, hadc] at h_M3a
    have h := not_lt.mp h_M3a
    nlinarith [h]
  have h₁₄ : o₁ * o₄ ≤ 0 := by
    rw [hbca] at h_M3b
    have h := not_lt.mp h_M3b
    linarith [h, (by ring : o₁ * o₄ = o₄ * o₁)]
  rcases four_reals_M2_M3_pair_sos hPluck h₂₄ h₁₃ h₂₃ h₁₄ with
    ⟨hO₁, hO₂⟩ | ⟨hO₃, hO₄⟩
  · exact orient2_all_zero_of_o1_o2_zero hcd hO₁ hO₂
  · exact orient2_all_zero_of_o3_o4_zero hab hO₃ hO₄

/-! ### Strong dichotomy: at least two matchings disjoint (noncollinear)

Combining the three pair-fail-implies-all-collinear lemmas, in the
noncollinear case we get the strong dichotomy: at least two of the three
matchings are geometrically disjoint.  Equivalently, the set of disjoint
matchings has cardinality at least two. -/

/-- Pair "at-least-one-disjoint" for `(M₁, M₂)`.  If the four points are not
all collinear, at least one of the matchings `(ab, cd)` or `(ac, bd)` is
geometrically disjoint. -/
theorem four_distinct_M1_or_M2_disjoint_noncollinear
    {a b c d : Point2}
    (hbc : b ≠ c) (had : a ≠ d)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d) ∨
    OrderedEdgesGeometricallyDisjoint (a, c) (b, d) := by
  by_contra h
  push_neg at h
  obtain ⟨hN1, hN2⟩ := h
  -- ¬ disjoint M_1 ⇒ both same-side witnesses for M_1 fail.
  have hM1a : ¬ (0 < orient2 a b c * orient2 a b d) := by
    intro hwitness
    exact hN1 (same_side_segments_disjoint hwitness)
  have hM1b : ¬ (0 < orient2 c d a * orient2 c d b) := by
    intro hwitness
    exact hN1 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  -- Similarly for M_2.
  have hM2a : ¬ (0 < orient2 a c b * orient2 a c d) := by
    intro hwitness
    exact hN2 (same_side_segments_disjoint hwitness)
  have hM2b : ¬ (0 < orient2 b d a * orient2 b d c) := by
    intro hwitness
    exact hN2 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  -- Apply M₁/M₂ pair-fail lemma: all four orient2 vanish.
  obtain ⟨h₄, h₃, h₂, h₁⟩ :=
    orient2_M1_M2_pair_fail_all_collinear hbc had hM1a hM1b hM2a hM2b
  -- Contradiction with hNotAllCollinear.
  rcases hNotAllCollinear with h | h | h | h
  · exact h h₄
  · exact h h₃
  · exact h h₂
  · exact h h₁

/-- Pair "at-least-one-disjoint" for `(M₁, M₃)`. -/
theorem four_distinct_M1_or_M3_disjoint_noncollinear
    {a b c d : Point2}
    (hbd : b ≠ d) (hac : a ≠ c)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    OrderedEdgesGeometricallyDisjoint (a, b) (c, d) ∨
    OrderedEdgesGeometricallyDisjoint (a, d) (b, c) := by
  by_contra h
  push_neg at h
  obtain ⟨hN1, hN3⟩ := h
  have hM1a : ¬ (0 < orient2 a b c * orient2 a b d) := by
    intro hwitness
    exact hN1 (same_side_segments_disjoint hwitness)
  have hM1b : ¬ (0 < orient2 c d a * orient2 c d b) := by
    intro hwitness
    exact hN1 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  have hM3a : ¬ (0 < orient2 a d b * orient2 a d c) := by
    intro hwitness
    exact hN3 (same_side_segments_disjoint hwitness)
  have hM3b : ¬ (0 < orient2 b c a * orient2 b c d) := by
    intro hwitness
    exact hN3 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  obtain ⟨h₄, h₃, h₂, h₁⟩ :=
    orient2_M1_M3_pair_fail_all_collinear hbd hac hM1a hM1b hM3a hM3b
  rcases hNotAllCollinear with h | h | h | h
  · exact h h₄
  · exact h h₃
  · exact h h₂
  · exact h h₁

/-- Pair "at-least-one-disjoint" for `(M₂, M₃)`. -/
theorem four_distinct_M2_or_M3_disjoint_noncollinear
    {a b c d : Point2}
    (hcd : c ≠ d) (hab : a ≠ b)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    OrderedEdgesGeometricallyDisjoint (a, c) (b, d) ∨
    OrderedEdgesGeometricallyDisjoint (a, d) (b, c) := by
  by_contra h
  push_neg at h
  obtain ⟨hN2, hN3⟩ := h
  have hM2a : ¬ (0 < orient2 a c b * orient2 a c d) := by
    intro hwitness
    exact hN2 (same_side_segments_disjoint hwitness)
  have hM2b : ¬ (0 < orient2 b d a * orient2 b d c) := by
    intro hwitness
    exact hN2 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  have hM3a : ¬ (0 < orient2 a d b * orient2 a d c) := by
    intro hwitness
    exact hN3 (same_side_segments_disjoint hwitness)
  have hM3b : ¬ (0 < orient2 b c a * orient2 b c d) := by
    intro hwitness
    exact hN3 (ordered_edges_geometrically_disjoint_symm (same_side_segments_disjoint hwitness))
  obtain ⟨h₄, h₃, h₂, h₁⟩ :=
    orient2_M2_M3_pair_fail_all_collinear hcd hab hM2a hM2b hM3a hM3b
  rcases hNotAllCollinear with h | h | h | h
  · exact h h₄
  · exact h h₃
  · exact h h₂
  · exact h h₁

/-- Strong four-point dichotomy.  For any four distinct points that are not
all collinear, at least two of the three perfect matchings of `K₄` are
geometrically disjoint.  Stated as a disjunction of the three possible "two
disjoint" combinations. -/
theorem four_distinct_points_two_matchings_disjoint_noncollinear
    {a b c d : Point2}
    (hab : a ≠ b) (had : a ≠ d) (hac : a ≠ c)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hNotAllCollinear :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    (OrderedEdgesGeometricallyDisjoint (a, b) (c, d) ∧
        OrderedEdgesGeometricallyDisjoint (a, c) (b, d)) ∨
    (OrderedEdgesGeometricallyDisjoint (a, b) (c, d) ∧
        OrderedEdgesGeometricallyDisjoint (a, d) (b, c)) ∨
    (OrderedEdgesGeometricallyDisjoint (a, c) (b, d) ∧
        OrderedEdgesGeometricallyDisjoint (a, d) (b, c)) := by
  rcases four_distinct_M1_or_M2_disjoint_noncollinear hbc had hNotAllCollinear with
    hD1 | hD2
  · rcases four_distinct_M1_or_M3_disjoint_noncollinear hbd hac hNotAllCollinear with
      hD1' | hD3
    · -- D1 holds; need to find D2 or D3 also.
      rcases four_distinct_M2_or_M3_disjoint_noncollinear hcd hab hNotAllCollinear with
        hD2 | hD3
      · exact Or.inl ⟨hD1, hD2⟩
      · exact Or.inr (Or.inl ⟨hD1, hD3⟩)
    · exact Or.inr (Or.inl ⟨hD1, hD3⟩)
  · -- D2 holds.
    rcases four_distinct_M2_or_M3_disjoint_noncollinear hcd hab hNotAllCollinear with
      hD2' | hD3
    · -- D2 already from hD2.  Need D1 or D3.
      rcases four_distinct_M1_or_M3_disjoint_noncollinear hbd hac hNotAllCollinear with
        hD1 | hD3
      · exact Or.inl ⟨hD1, hD2⟩
      · exact Or.inr (Or.inr ⟨hD2, hD3⟩)
    · exact Or.inr (Or.inr ⟨hD2, hD3⟩)

/-! ### K4 wrap: missing-edge helper + noncollinear bound

If two unordered edges have geometrically disjoint segments, then at least one
of them is missing from any Conway thrackle's unordered support.  This is
the elementary lemma that converts the strong dichotomy into a missing-edge
count, which in turn bounds `unorderedEdgeSupport` cardinality. -/

/-- If two unordered edges of an underlying point set have geometrically
disjoint segments (and the unordered edges themselves are distinct), then at
least one of them is missing from any Conway thrackle's unordered support. -/
theorem unordered_edge_missing_of_geometrically_disjoint
    {E : Finset (Point2 × Point2)} (hConway : IsConwayThrackle E)
    {p q r s : Point2}
    (hpq_rs : (Sym2.mk ((p, q) : Point2 × Point2)) ≠ Sym2.mk ((r, s) : Point2 × Point2))
    (hDisj : OrderedEdgesGeometricallyDisjoint (p, q) (r, s)) :
    (Sym2.mk ((p, q) : Point2 × Point2)) ∉ unorderedEdgeSupport E ∨
    (Sym2.mk ((r, s) : Point2 × Point2)) ∉ unorderedEdgeSupport E := by
  by_contra h
  push_neg at h
  obtain ⟨hu, hv⟩ := h
  rw [mem_unorderedEdgeSupport_iff] at hu hv
  obtain ⟨e, heE, hue⟩ := hu
  obtain ⟨f, hfE, hvf⟩ := hv
  have hef : e ≠ f := by
    intro habs
    apply hpq_rs
    rw [← hue, ← hvf, habs]
  have hSimple : OrderedEdgesMeetSimply e f := hConway e heE f hfE hef
  obtain ⟨x, hxef, _huniq⟩ := hSimple
  apply hDisj
  refine ⟨x, ?_, ?_⟩
  · have hueq := hue
    unfold unorderedEdgeOfOrdered at hueq
    rw [Sym2.mk_eq_mk_iff] at hueq
    rcases hueq with he_eq | he_eq
    · rw [he_eq] at hxef
      exact hxef.1
    · rw [he_eq] at hxef
      exact on_closed_segment_symm hxef.1
  · have hveq := hvf
    unfold unorderedEdgeOfOrdered at hveq
    rw [Sym2.mk_eq_mk_iff] at hveq
    rcases hveq with hf_eq | hf_eq
    · rw [hf_eq] at hxef
      exact hxef.2
    · rw [hf_eq] at hxef
      exact on_closed_segment_symm hxef.2

/-- The standard six-pair Finset of unordered pairs from four points. -/
noncomputable def sixUnorderedPairs (a b c d : Point2) : Finset (Sym2 Point2) :=
  {Sym2.mk ((a, b) : Point2 × Point2), Sym2.mk ((a, c) : Point2 × Point2),
   Sym2.mk ((a, d) : Point2 × Point2), Sym2.mk ((b, c) : Point2 × Point2),
   Sym2.mk ((b, d) : Point2 × Point2), Sym2.mk ((c, d) : Point2 × Point2)}

/-- Cardinality of the six-element set of unordered pairs from four distinct
points.  This is the standard pigeonhole "container" for any unordered edge
support on a four-point ambient set. -/
theorem six_unordered_pairs_card_eq_six
    {a b c d : Point2}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (sixUnorderedPairs a b c d).card = 6 := by
  classical
  unfold sixUnorderedPairs
  -- The six `Sym2.mk` values are pairwise distinct via `Sym2.eq_iff`.
  have h_ab_ac : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((a, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hbc h2
    · exact hac h1
  have h_ab_ad : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hbd h2
    · exact had h1
  have h_ab_bc : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_ab_bd : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact had h1
  have h_ab_cd : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hac h1
    · exact had h1
  have h_ac_ad : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hcd h2
    · exact had h1
  have h_ac_bc : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_ac_bd : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact had h1
  have h_ac_cd : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hac h1
    · exact had h1
  have h_ad_bc : Sym2.mk ((a, d) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_ad_bd : Sym2.mk ((a, d) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact had h1
  have h_ad_cd : Sym2.mk ((a, d) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hac h1
    · exact had h1
  have h_bc_bd : Sym2.mk ((b, c) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hcd h2
    · exact hbd h1
  have h_bc_cd : Sym2.mk ((b, c) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hbc h1
    · exact hbd h1
  have h_bd_cd : Sym2.mk ((b, d) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hbc h1
    · exact hbd h1
  -- Now compute the cardinality using the distinctness facts.
  simp [h_ab_ac, h_ab_ad, h_ab_bc, h_ab_bd, h_ab_cd,
        h_ac_ad, h_ac_bc, h_ac_bd, h_ac_cd,
        h_ad_bc, h_ad_bd, h_ad_cd,
        h_bc_bd, h_bc_cd, h_bd_cd]

/-- Counting helper: if `S` is contained in a six-element Finset `T`, and two
distinct elements `m₁, m₂ ∈ T` are not in `S`, then `|S| ≤ 4`. -/
theorem card_le_four_of_two_missing
    {S T : Finset (Sym2 Point2)}
    (hsub : S ⊆ T) (hTcard : T.card = 6)
    {m₁ m₂ : Sym2 Point2}
    (hm₁T : m₁ ∈ T) (hm₂T : m₂ ∈ T)
    (hm₁_ne : m₁ ≠ m₂)
    (hm₁_notS : m₁ ∉ S) (hm₂_notS : m₂ ∉ S) :
    S.card ≤ 4 := by
  classical
  have hSsub : S ⊆ T \ {m₁, m₂} := by
    intro x hxS
    refine Finset.mem_sdiff.mpr ⟨hsub hxS, ?_⟩
    intro hx_pair
    rcases Finset.mem_insert.mp hx_pair with hx | hx
    · exact hm₁_notS (hx ▸ hxS)
    · rw [Finset.mem_singleton] at hx
      exact hm₂_notS (hx ▸ hxS)
  have hPairCard : ({m₁, m₂} : Finset (Sym2 Point2)).card = 2 := by
    simp [hm₁_ne]
  have hPairSub : ({m₁, m₂} : Finset (Sym2 Point2)) ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact hx ▸ hm₁T
    · rw [Finset.mem_singleton] at hx
      exact hx ▸ hm₂T
  have hDiffCard : (T \ ({m₁, m₂} : Finset (Sym2 Point2))).card = 4 := by
    rw [Finset.card_sdiff_of_subset hPairSub, hTcard, hPairCard]
  have h := Finset.card_le_card hSsub
  rw [hDiffCard] at h
  exact h

/-- Noncollinear Conway-conditioned K4 bound, conditional version.  Assuming
the unordered edge support is contained in the standard six-pair Finset for
four ambient distinct points, and assuming not-all-collinear, we conclude
`|unorderedEdgeSupport E| ≤ 4`.

The conditional shape lets us decouple the (long) casework for the
subset-inclusion hypothesis from the strong dichotomy + Conway argument.
The unconditional version follows once the subset inclusion is established
by enumeration on `A.card = 4`. -/
theorem exact_fourpoint_conway_thrackle_support_bound_conditional
    {a b c d : Point2}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {E : Finset (Point2 × Point2)}
    (hConway : IsConwayThrackle E)
    (hsub : unorderedEdgeSupport E ⊆ sixUnorderedPairs a b c d)
    (hNotAllCol :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0) :
    (unorderedEdgeSupport E).card ≤ 4 := by
  classical
  have hTcard : (sixUnorderedPairs a b c d).card = 6 :=
    six_unordered_pairs_card_eq_six hab hac had hbc hbd hcd
  -- All six unordered pairs of {a, b, c, d} are members of sixUnorderedPairs.
  have hAB_mem : Sym2.mk ((a, b) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  have hAC_mem : Sym2.mk ((a, c) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  have hAD_mem : Sym2.mk ((a, d) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  have hBC_mem : Sym2.mk ((b, c) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  have hBD_mem : Sym2.mk ((b, d) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  have hCD_mem : Sym2.mk ((c, d) : Point2 × Point2) ∈ sixUnorderedPairs a b c d := by
    simp [sixUnorderedPairs]
  -- Inequalities between specific Sym2 pairs.  Each is proved by unpacking
  -- `Sym2.eq_iff` and contradicting with one of the six distinctness facts.
  have h_AB_CD : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((c, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hac h1
    · exact had h1
  have h_AC_BD : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact had h1
  have h_AD_BC : Sym2.mk ((a, d) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_AB_AC : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((a, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hbc h2
    · exact hac h1
  have h_AB_AD : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hbd h2
    · exact had h1
  have h_AB_BD : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact had h1
  have h_AB_BC : Sym2.mk ((a, b) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_CD_AC : Sym2.mk ((c, d) : Point2 × Point2) ≠ Sym2.mk ((a, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hac h1.symm
    · exact had h2.symm
  have h_CD_BD : Sym2.mk ((c, d) : Point2 × Point2) ≠ Sym2.mk ((b, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hbc h1.symm
    · exact hcd h1
  have h_CD_AD : Sym2.mk ((c, d) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hac h1.symm
    · exact hcd h1
  have h_CD_BC : Sym2.mk ((c, d) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hbc h1.symm
    · exact hbd h2.symm
  have h_AC_AD : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hcd h2
    · exact had h1
  have h_AC_BC : Sym2.mk ((a, c) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1
    · exact hac h1
  have h_BD_AD : Sym2.mk ((b, d) : Point2 × Point2) ≠ Sym2.mk ((a, d) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hab h1.symm
    · exact hbd h1
  have h_BD_BC : Sym2.mk ((b, d) : Point2 × Point2) ≠ Sym2.mk ((b, c) : Point2 × Point2) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hcd h2.symm
    · exact hbc h1
  -- Now the strong dichotomy.
  rcases four_distinct_points_two_matchings_disjoint_noncollinear hab had hac hbc hbd hcd hNotAllCol with
    ⟨hD1, hD2⟩ | ⟨hD1, hD3⟩ | ⟨hD2, hD3⟩
  -- For brevity we package each case below as a small "two missing edges" derivation.
  · -- M_1 and M_2 disjoint.
    rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AB_CD hD1 with hMA | hMA
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AC_BD hD2 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hAB_mem hAC_mem h_AB_AC hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hAB_mem hBD_mem h_AB_BD hMA hMB
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AC_BD hD2 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hCD_mem hAC_mem h_CD_AC hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hCD_mem hBD_mem h_CD_BD hMA hMB
  · -- M_1 and M_3 disjoint.
    rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AB_CD hD1 with hMA | hMA
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AD_BC hD3 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hAB_mem hAD_mem h_AB_AD hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hAB_mem hBC_mem h_AB_BC hMA hMB
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AD_BC hD3 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hCD_mem hAD_mem h_CD_AD hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hCD_mem hBC_mem h_CD_BC hMA hMB
  · -- M_2 and M_3 disjoint.
    rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AC_BD hD2 with hMA | hMA
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AD_BC hD3 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hAC_mem hAD_mem h_AC_AD hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hAC_mem hBC_mem h_AC_BC hMA hMB
    · rcases unordered_edge_missing_of_geometrically_disjoint hConway h_AD_BC hD3 with hMB | hMB
      · exact card_le_four_of_two_missing hsub hTcard hBD_mem hAD_mem h_BD_AD hMA hMB
      · exact card_le_four_of_two_missing hsub hTcard hBD_mem hBC_mem h_BD_BC hMA hMB

/-- Subset-inclusion bookkeeping.  For a four-point ambient set `A = {a,b,c,d}`
and an edge set `E` whose endpoints are in `A`, the unordered support of `E`
is contained in the standard six-pair `sixUnorderedPairs a b c d`. -/
theorem unorderedEdgeSupport_subset_sixUnorderedPairs_of_card_eq_four
    {A : Finset Point2} {E : Finset (Point2 × Point2)}
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2)
    {a b c d : Point2}
    (hAeq : A = ({a, b, c, d} : Finset Point2)) :
    unorderedEdgeSupport E ⊆ sixUnorderedPairs a b c d := by
  classical
  intro u hu
  unfold unorderedEdgeSupport at hu
  rw [Finset.mem_image] at hu
  rcases hu with ⟨e, heE, heu⟩
  have heData := hEdges e heE
  rw [hAeq] at heData
  cases e with
  | mk p q =>
    simp at heData heu
    have hp : p = a ∨ p = b ∨ p = c ∨ p = d := by simpa using heData.1
    have hq : q = a ∨ q = b ∨ q = c ∨ q = d := by simpa using heData.2.1
    have hpq : p ≠ q := heData.2.2
    rw [← heu]
    rcases hp with hp | hp | hp | hp <;> rcases hq with hq | hq | hq | hq
    -- 16 cases.  4 diagonal collapse to False; 12 non-diagonal map to one
    -- of the six elements of sixUnorderedPairs (six direct, six via swap).
    all_goals (try (subst p; subst q; exact False.elim (hpq rfl)))
    all_goals (subst p; subst q)
    all_goals (simp [sixUnorderedPairs, unorderedEdgeOfOrdered])

/-- Repeated-argument orientation vanishing.  When two of the three arguments
of `orient2` are equal, the result is zero. -/
theorem orient2_eq_zero_of_two_eq_first
    (a b : Point2) : orient2 a a b = 0 := by
  unfold orient2; ring

theorem orient2_eq_zero_of_two_eq_second
    (a b : Point2) : orient2 a b a = 0 := by
  unfold orient2; ring

theorem orient2_eq_zero_of_two_eq_third
    (a b : Point2) : orient2 a b b = 0 := by
  unfold orient2; ring

/-- If all four "canonical" orient2 values on `{a, b, c, d}` vanish, then
every triple `(p, q, r)` with `p, q, r ∈ {a, b, c, d}` has `orient2 p q r = 0`.
This is the key bridge between the 4-orient form of "noncollinear" and the
full "every triple from A is collinear" form. -/
theorem orient2_zero_of_quadruple_zero
    {a b c d : Point2}
    (h_abc : orient2 a b c = 0) (h_abd : orient2 a b d = 0)
    (h_acd : orient2 a c d = 0) (h_bcd : orient2 b c d = 0)
    {p q r : Point2}
    (hp : p = a ∨ p = b ∨ p = c ∨ p = d)
    (hq : q = a ∨ q = b ∨ q = c ∨ q = d)
    (hr : r = a ∨ r = b ∨ r = c ∨ r = d) :
    orient2 p q r = 0 := by
  -- Derive the additional orient2 zeros at every permutation by cyclic/swap.
  have h_acb : orient2 a c b = 0 := by
    have := orient2_swap₂₃ a b c; linarith
  have h_adb : orient2 a d b = 0 := by
    have := orient2_swap₂₃ a b d; linarith
  have h_adc : orient2 a d c = 0 := by
    have := orient2_swap₂₃ a c d; linarith
  have h_bdc : orient2 b d c = 0 := by
    have := orient2_swap₂₃ b c d; linarith
  have h_bac : orient2 b a c = 0 := by
    have := orient2_swap₁₂ a b c; linarith
  have h_bad : orient2 b a d = 0 := by
    have := orient2_swap₁₂ a b d; linarith
  have h_cab : orient2 c a b = 0 := by
    have := orient2_cyclic' a b c; linarith
  have h_cad : orient2 c a d = 0 := by
    have := orient2_swap₁₂ a c d; linarith
  have h_cba : orient2 c b a = 0 := by
    have := orient2_swap₁₃ a b c; linarith
  have h_cbd : orient2 c b d = 0 := by
    have := orient2_swap₁₂ b c d; linarith
  have h_cda : orient2 c d a = 0 := by
    have := orient2_cyclic a c d; linarith
  have h_cdb : orient2 c d b = 0 := by
    have := orient2_cyclic b c d; linarith
  have h_dab : orient2 d a b = 0 := by
    have := orient2_cyclic' a b d; linarith
  have h_dac : orient2 d a c = 0 := by
    have := orient2_cyclic' a c d; linarith
  have h_dba : orient2 d b a = 0 := by
    have := orient2_swap₁₃ a b d; linarith
  have h_dbc : orient2 d b c = 0 := by
    have := orient2_cyclic d b c; linarith
  have h_dca : orient2 d c a = 0 := by
    have := orient2_swap₁₃ a c d; linarith
  have h_dcb : orient2 d c b = 0 := by
    have := orient2_swap₁₃ b c d; linarith
  have h_bca : orient2 b c a = 0 := by
    have := orient2_cyclic a b c; linarith
  have h_bda : orient2 b d a = 0 := by
    have := orient2_cyclic a b d; linarith
  have h_acd' : orient2 a c d = 0 := h_acd
  -- Case-split on each of p, q, r.
  rcases hp with hp | hp | hp | hp <;>
    rcases hq with hq | hq | hq | hq <;>
      rcases hr with hr | hr | hr | hr <;>
        subst_vars
  all_goals
    first
    | exact h_abc | exact h_abd | exact h_acd | exact h_bcd
    | exact h_acb | exact h_adb | exact h_adc | exact h_bdc
    | exact h_bac | exact h_bad | exact h_cab | exact h_cad
    | exact h_cba | exact h_cbd | exact h_cda | exact h_cdb
    | exact h_dab | exact h_dac | exact h_dba | exact h_dbc
    | exact h_dca | exact h_dcb | exact h_bca | exact h_bda
    | exact orient2_eq_zero_of_two_eq_first _ _
    | exact orient2_eq_zero_of_two_eq_second _ _
    | exact orient2_eq_zero_of_two_eq_third _ _

/-- Unconditional noncollinear Conway-conditioned K4 bound.  Combines
`unorderedEdgeSupport_subset_sixUnorderedPairs_of_card_eq_four` with the
conditional version `exact_fourpoint_conway_thrackle_support_bound_conditional`. -/
theorem exact_fourpoint_conway_thrackle_support_bound_noncollinear_thm
    {A : Finset Point2} {E : Finset (Point2 × Point2)}
    (hEdges : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2)
    (hConway : IsConwayThrackle E)
    (hAcard : A.card = 4)
    (hNotAllCol : ¬ ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, orient2 p q r = 0) :
    (unorderedEdgeSupport E).card ≤ A.card := by
  classical
  rcases Finset.card_eq_four.mp hAcard with
    ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hAeq⟩
  have hsub : unorderedEdgeSupport E ⊆ sixUnorderedPairs a b c d :=
    unorderedEdgeSupport_subset_sixUnorderedPairs_of_card_eq_four hEdges hAeq
  have hNotAllCol4 :
      orient2 a b c ≠ 0 ∨ orient2 a b d ≠ 0 ∨
      orient2 a c d ≠ 0 ∨ orient2 b c d ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨h_abc, h_abd, h_acd, h_bcd⟩ := h
    apply hNotAllCol
    intro p hp q hq r hr
    rw [hAeq] at hp hq hr
    simp at hp hq hr
    exact orient2_zero_of_quadruple_zero h_abc h_abd h_acd h_bcd hp hq hr
  have hLE := exact_fourpoint_conway_thrackle_support_bound_conditional
    hab hac had hbc hbd hcd hConway hsub hNotAllCol4
  rw [hAcard]
  exact hLE

/-! ### Bridge documentation (continued)

For brevity we prove only the `M₁/M₃` algebraic pair lemma in this layer;
the symmetric `M₁/M₂` and `M₂/M₃` pair lemmas are scheduled for the next
tightening session.  Each follows the same SOS-Plücker pattern with two
hypothesised sign-products from each matching's witnesses.

### Session 2026-05-23 status (one-shot dichotomy attempt)

This block delivers the algebraic + geometric *one-shot* foundation for the
Conway-conditioned 4-point K4 obstruction, replacing the existing
`ExactFourPointK4ObstructionCertificate` (which is provably false on
all-collinear 4-point configurations because overlap counts as "meeting"
under `OrderedEdgesGeometricallyDisjoint`, yet provides no disjoint pair).

What is proved in this layer:

* `four_reals_orientation_dichotomy_alg`: algebraic SOS dichotomy.  Under
  Plücker on four reals, the six bilinear sign witnesses cannot all fail
  simultaneously unless all four reals vanish.
* `four_points_orientation_dichotomy`: geometric instantiation.  For any
  four points not all collinear, at least one of the six `same_side`
  disjointness witnesses for the three perfect matchings holds.
* `four_distinct_points_one_matching_disjoint_noncollinear`: at least one
  matching is geometrically disjoint when the four points are noncollinear.
* `ExactFourPointConwayThrackleSupportBoundCertificate`: corrected target
  (Conway-conditioned).
* `CollinearFourPointConwayResidual`: all-collinear residual stated
  separately for follow-up.
* `four_reals_M1_M3_pair_sos`: algebraic pair lemma for the `M₁/M₃`
  matchings.  Joint failure gives `o₁ = o₃ = 0` or `o₂ = o₄ = 0`.
* `orient2_zero_two_zeros_share_bd`: geometric closure.  Two zero
  orientations sharing a `b, d` vertex pair with `b ≠ d` force a third
  zero orientation, hence all four points are collinear when distinct.

What is pending for future sessions:

1. `four_reals_M1_M2_pair_sos` and `four_reals_M2_M3_pair_sos`: symmetric
   pair lemmas.  Each follows the same SOS-with-Plücker pattern.
2. `four_distinct_points_two_matchings_disjoint_noncollinear`: combine the
   three pair lemmas plus the original dichotomy to conclude at least two
   matchings disjoint.
3. `exact_fourpoint_conway_thrackle_support_bound_noncollinear`: use the
   strong dichotomy to bound `|unorderedEdgeSupport E| ≤ 4` for noncollinear
   four-point Conway thrackles with no incident vertex.
4. Discharge `CollinearFourPointConwayResidual` by sorting on the supporting
   line and counting which pairs of unordered edges can share at most one
   point.
5. Combine 3 and 4 into `exact_fourpoint_conway_thrackle_support_bound_thm`,
   then lift through the existing `fivepoint`/`sixpoint` boundary chain to
   close `LargeNonStarConwayThrackleSupportBound` and ultimately
   `ConwayThrackleSupportBound`.  -/

/-- Five-point-or-larger non-star support certificate.  This is the genuinely
large part of the remaining straight-line thrackle theorem after the exact
four-vertex boundary is separated. -/
def FivePointNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      5 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Exact five-vertex non-star support certificate.  Kept separate from the
large theorem so finite boundary geometry can be attacked independently. -/
def ExactFivePointNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      A.card = 5 →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Six-point-or-larger non-star support certificate. -/
def SixPointNonStarThrackleSupportBoundCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ E : Finset (Point2 × Point2),
      (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
      (∀ e ∈ E, ∀ f ∈ E, ¬ OrderedEdgesGeometricallyDisjoint e f) →
      6 ≤ A.card →
      (∀ v : Point2, ¬ OrderedEdgesIncidentTo v E) →
        (unorderedEdgeSupport E).card ≤ A.card

/-- Exact five-point support plus the six-point-or-larger residual supplies the
five-point-or-larger non-star support theorem. -/
theorem fivepoint_nonstar_support_bound_from_exact_five_and_six_residual
    (hExact5 : ExactFivePointNonStarThrackleSupportBoundCertificate)
    (hSix : SixPointNonStarThrackleSupportBoundCertificate) :
    FivePointNonStarThrackleSupportBoundCertificate := by
  intro A E hEdges hNoDisj hA5 hNonStar
  by_cases hEq5 : A.card = 5
  · exact hExact5 A E hEdges hNoDisj hEq5 hNonStar
  · have hA6 : 6 ≤ A.card := by omega
    exact hSix A E hEdges hNoDisj hA6 hNonStar

/-- Exact four-vertex support plus the five-point-or-larger residual supplies
the four-point-or-larger non-star support theorem. -/
theorem fourpoint_nonstar_support_bound_from_exact_four_and_five_residual
    (hExact4 : ExactFourPointNonStarThrackleSupportBoundCertificate)
    (hFive : FivePointNonStarThrackleSupportBoundCertificate) :
    FourPointNonStarThrackleSupportBoundCertificate := by
  intro A E hEdges hNoDisj hA4 hNonStar
  by_cases hEq4 : A.card = 4
  · exact hExact4 A E hEdges hNoDisj hEq4 hNonStar
  · have hA5 : 5 ≤ A.card := by omega
    exact hFive A E hEdges hNoDisj hA5 hNonStar

/-- Closing the four-point-or-larger residual closes the large non-star support
residual, because the three-point case is a finite triangle bound. -/
theorem large_nonstar_support_bound_from_fourpoint_residual
    (hFour : FourPointNonStarThrackleSupportBoundCertificate) :
    LargeNonStarThrackleSupportBoundCertificate := by
  intro A E hEdges hNoDisj hA3 hNonStar
  by_cases hAcard3 : A.card = 3
  · exact unordered_support_card_le_of_card_eq_three hAcard3 hEdges
  · have hA4 : 4 ≤ A.card := by omega
    exact hFour A E hEdges hNoDisj hA4 hNonStar

/-- The cardinal large-non-star residual supplies the endpoint-charge residual,
because finite cardinal comparison produces an injection. -/
theorem large_nonstar_endpoint_charging_from_support_bound
    (hSupport : LargeNonStarThrackleSupportBoundCertificate) :
    LargeNonStarThrackleEndpointChargingCertificate := by
  intro A E hEdges hNoDisj hA3 hNonStar
  exact endpoint_charge_of_support_card_le
    (hSupport A E hEdges hNoDisj hA3 hNonStar)

/-- Closing all large non-star systems closes the non-star residual, because the
small systems are automatically stars. -/
theorem nonstar_thrackle_endpoint_charging_from_large_residual
    (hLarge : LargeNonStarThrackleEndpointChargingCertificate) :
    NonStarThrackleEndpointChargingCertificate := by
  intro A E hEdges hNoDisj hNonStar
  by_cases hA2 : A.card ≤ 2
  · rcases exists_incident_vertex_of_card_le_two hA2 hEdges with ⟨v, hIncident⟩
    exact False.elim (hNonStar v hIncident)
  · have hA3 : 3 ≤ A.card := by omega
    exact hLarge A E hEdges hNoDisj hA3 hNonStar

/-- Star closure plus the non-star residual certificate gives the full
endpoint-charging form of the straight-line thrackle theorem. -/
theorem thrackle_endpoint_charging_from_nonstar_residual
    (hNonStar : NonStarThrackleEndpointChargingCertificate) :
    ThrackleEndpointChargingCertificate := by
  intro A E hEdges hNoDisj
  by_cases hStar : ∃ v : Point2, OrderedEdgesIncidentTo v E
  · rcases hStar with ⟨v, hIncident⟩
    exact endpoint_charging_of_incident_vertex hEdges hIncident
  · exact hNonStar A E hEdges hNoDisj (by
      intro v hIncident
      exact hStar ⟨v, hIncident⟩)

/-- Star systems and `|A| ≤ 2` systems are closed.  Therefore a large non-star
endpoint-charge certificate is enough for the full straight-line thrackle
endpoint-charge theorem. -/
theorem thrackle_endpoint_charging_from_large_nonstar_residual
    (hLarge : LargeNonStarThrackleEndpointChargingCertificate) :
    ThrackleEndpointChargingCertificate :=
  thrackle_endpoint_charging_from_nonstar_residual
    (nonstar_thrackle_endpoint_charging_from_large_residual hLarge)

/-- Cardinal support bound on large non-star systems is enough for the full
endpoint-charging form of straight-line thrackle. -/
theorem thrackle_endpoint_charging_from_large_nonstar_support_bound
    (hSupport : LargeNonStarThrackleSupportBoundCertificate) :
    ThrackleEndpointChargingCertificate :=
  thrackle_endpoint_charging_from_large_nonstar_residual
    (large_nonstar_endpoint_charging_from_support_bound hSupport)

/-- A cardinal support bound for four-point-or-larger non-star systems is enough
for the full endpoint-charging form of straight-line thrackle. -/
theorem thrackle_endpoint_charging_from_fourpoint_nonstar_support_bound
    (hFour : FourPointNonStarThrackleSupportBoundCertificate) :
    ThrackleEndpointChargingCertificate :=
  thrackle_endpoint_charging_from_large_nonstar_support_bound
    (large_nonstar_support_bound_from_fourpoint_residual hFour)

/-- The endpoint-charging certificate implies the pointwise undirected thrackle
support theorem by finite cardinality.  This isolates the remaining geometric
content of the classical thrackle input. -/
theorem pointwise_thrackle_support_from_endpoint_charging
    (h : ThrackleEndpointChargingCertificate) :
    PointwiseUndirectedThrackleSupportBound := by
  intro A E hEdges hNoDisj
  obtain ⟨charge, hInjective⟩ := h A E hEdges hNoDisj
  have hcard := Fintype.card_le_of_injective charge hInjective
  simpa using hcard

/-- The pointwise straight-line thrackle support theorem implies the eventual
form used by the Erdős #132 reduction. -/
theorem undirected_thrackle_support_from_pointwise
    (h : PointwiseUndirectedThrackleSupportBound) :
    UndirectedThrackleSupportBound := by
  filter_upwards with n
  intro A _hA E hEdges hNoDisj
  exact h A E hEdges hNoDisj

/-- Orientation fibers are at most two for the edge sets relevant to the
thrackle bridge.  Kept as a named finite bridge until the preferred unordered
edge API is expanded. -/
def OrderedOrientationFiberBound : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ E : Finset (Point2 × Point2),
          (∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2) →
            OrientationFiberAtMostTwo E

/-- Undirected thrackle support plus orientation bookkeeping implies the
ordered thrackle bound used by the diameter shell proof. -/
theorem ordered_thrackle_bound_from_undirected_support
    (hSupport : UndirectedThrackleSupportBound)
    (hOrient : OrderedOrientationFiberBound) :
    OrderedThrackleBound := by
  filter_upwards [hSupport, hOrient] with n hSupportN hOrientN
  intro A hA E hEdges hNoDisj
  have hOrdered : E.card ≤ 2 * (unorderedEdgeSupport E).card :=
    ordered_card_le_two_mul_unordered_support E (hOrientN A hA E hEdges)
  have hSupportCard : (unorderedEdgeSupport E).card ≤ A.card :=
    hSupportN A hA E hEdges hNoDisj
  exact le_trans hOrdered (Nat.mul_le_mul_left 2 hSupportCard)

/-- Since orientation fibers are universally bounded by two, the undirected
support theorem alone implies the ordered thrackle bound. -/
theorem ordered_thrackle_bound_from_undirected_support_only
    (hSupport : UndirectedThrackleSupportBound) :
    OrderedThrackleBound := by
  filter_upwards [hSupport] with n hSupportN
  intro A hA E hEdges hNoDisj
  have hOrdered : E.card ≤ 2 * (unorderedEdgeSupport E).card :=
    ordered_card_le_two_mul_unordered_support E (orientation_fiber_at_most_two E)
  have hSupportCard : (unorderedEdgeSupport E).card ≤ A.card :=
    hSupportN A hA E hEdges hNoDisj
  exact le_trans hOrdered (Nat.mul_le_mul_left 2 hSupportCard)

/-- Hopf-Pannwitz ordered multiplicity follows from no-disjoint-diameter-edges
plus the ordered thrackle bound. -/
theorem diameter_ordered_bound_from_thrackle_components
    (hNoDisjoint : NoDisjointDiameterEdges)
    (hThrackle : OrderedThrackleBound) :
    DiameterShellOrderedMultiplicityBound := by
  filter_upwards [hNoDisjoint, hThrackle] with n hNoDisjointN hThrackleN
  intro A hA Δ hΔ
  have hEdges :
      ∀ e ∈ diameterOrderedEdges A Δ,
        e.1 ∈ A ∧ e.2 ∈ A ∧ e.1 ≠ e.2 := by
    intro e he
    unfold diameterOrderedEdges orderedPairEvents at he
    have he' := Finset.mem_filter.mp he
    have hp := Finset.mem_filter.mp he'.1
    have hprod := Finset.mem_product.mp hp.1
    exact ⟨hprod.1, hprod.2, hp.2⟩
  have hNoDisj :
      ∀ e ∈ diameterOrderedEdges A Δ,
        ∀ f ∈ diameterOrderedEdges A Δ,
          ¬ OrderedEdgesGeometricallyDisjoint e f :=
    hNoDisjointN A hA Δ hΔ
  simpa [orderedShellMultiplicity_eq_diameterOrderedEdges_card] using
    hThrackleN A hA (diameterOrderedEdges A Δ) hEdges hNoDisj

/-- Hopf-Pannwitz diameter sparsity follows from the two thrackle components. -/
theorem diameter_shell_sparse_from_thrackle_components
    (hNoDisjoint : NoDisjointDiameterEdges)
    (hThrackle : OrderedThrackleBound) :
    DiameterShellSparseBound :=
  diameter_shell_sparse_from_ordered_bound
    (diameter_ordered_bound_from_thrackle_components hNoDisjoint hThrackle)

/-- Diameter shell existence is finite bookkeeping: for all sufficiently large
cardinalities, a finite ordered distance spectrum is nonempty and therefore has
a maximum. -/
theorem diameter_shell_exists_eventually_holds :
    DiameterShellExistsEventually := by
  unfold DiameterShellExistsEventually
  rw [Filter.eventually_atTop]
  refine ⟨2, ?_⟩
  intro n hn A hA
  have hcard : 1 < A.card := by omega
  rcases Finset.one_lt_card.mp hcard with ⟨a, ha, b, hb, hne⟩
  have hpq : (a, b) ∈ orderedPairEvents A := by
    unfold orderedPairEvents
    simp [ha, hb, hne]
  have hspec_nonempty : (orderedDistanceSpectrum A).Nonempty := by
    unfold orderedDistanceSpectrum
    exact ⟨dist a b, Finset.mem_image.mpr ⟨(a, b), hpq, rfl⟩⟩
  let Δ := (orderedDistanceSpectrum A).max' hspec_nonempty
  refine ⟨Δ, ?_⟩
  exact ⟨Finset.max'_mem _ _, fun s hs => Finset.le_max' _ s hs⟩

/-- Hopf-Pannwitz split into maximum-existence plus diameter sparsity. -/
structure HopfPannwitzComponentPack : Prop where
  diameter_exists : DiameterShellExistsEventually
  diameter_sparse : DiameterShellSparseBound

/-- The component version of Hopf-Pannwitz supplies the current bridge. -/
theorem hopf_pannwitz_ordered_from_components
    (H : HopfPannwitzComponentPack) :
    HopfPannwitzOrderedDiameterBound := by
  filter_upwards [H.diameter_exists, H.diameter_sparse] with n hExists hSparse
  intro A hA
  rcases hExists A hA with ⟨Δ, hΔ⟩
  exact ⟨Δ, hΔ, hSparse A hA Δ hΔ⟩

/-- Since diameter-shell existence is now proved, Hopf-Pannwitz reduces to the
diameter-sparsity theorem. -/
theorem hopf_pannwitz_ordered_from_diameter_sparsity
    (hSparse : DiameterShellSparseBound) :
    HopfPannwitzOrderedDiameterBound :=
  hopf_pannwitz_ordered_from_components
    ⟨diameter_shell_exists_eventually_holds, hSparse⟩

theorem erdos132_from_hopf_pannwitz_and_flux
    (hHP : HopfPannwitzOrderedDiameterBound)
    (hFlux : SecondSparseShellFluxBridge) :
    Erdos132Ordered := by
  filter_upwards [hHP, hFlux] with n hHPn hFluxn
  intro A hA
  rcases hHPn A hA with ⟨Δ, hΔdiam, hΔsparse⟩
  rcases hFluxn A hA Δ hΔdiam with ⟨r, hr_ne, hr_sparse⟩
  exact ⟨Δ, r, hr_ne.symm, hΔsparse, hr_sparse⟩

/-! ## Component bridge decomposition from the final reduction plan -/

/-- Number of occupied shells in the ordered distance spectrum. -/
noncomputable def occupiedShellCount (A : Finset Point2) : ℕ :=
  (orderedDistanceSpectrum A).card

/-- Total ordered two-body ledger capacity. -/
noncomputable def totalOrderedPairBudget (A : Finset Point2) : ℕ :=
  (orderedPairEvents A).card

/-- The ordered event budget is bounded by all ordered pairs. -/
theorem totalOrderedPairBudget_le_all_pairs (A : Finset Point2) :
    totalOrderedPairBudget A ≤ A.card * A.card := by
  classical
  unfold totalOrderedPairBudget orderedPairEvents
  calc
    (((A.product A).filter (fun pq => pq.1 ≠ pq.2)).card) ≤
        (A.product A).card := Finset.card_filter_le _ _
    _ = A.card * A.card := by simp

/-- A single shell cannot contain more ordered events than the whole ordered
pair budget. -/
theorem orderedShellMultiplicity_le_budget (A : Finset Point2) (r : ℝ) :
    orderedShellMultiplicity A r ≤ totalOrderedPairBudget A := by
  classical
  unfold orderedShellMultiplicity totalOrderedPairBudget
  exact Finset.card_filter_le _ _

/-- If a shell lies in the spectrum, then it has positive ordered occupancy. -/
theorem orderedShellMultiplicity_pos_of_mem
    {A : Finset Point2} {r : ℝ}
    (hr : r ∈ orderedDistanceSpectrum A) :
    0 < orderedShellMultiplicity A r := by
  classical
  unfold orderedDistanceSpectrum orderedShellMultiplicity at *
  rw [Finset.mem_image] at hr
  rcases hr with ⟨pq, hpq, hpq_r⟩
  apply Finset.card_pos.mpr
  exact ⟨pq, by simp [hpq, hpq_r]⟩

/-- An occupied shell that is not sparse is supercritical in the ordered
normalization. -/
theorem orderedShellMultiplicity_supercritical_of_not_sparse
    {A : Finset Point2} {r : ℝ}
    (hr : r ∈ orderedDistanceSpectrum A)
    (hnot : ¬ SparseShell A r) :
    2 * A.card < orderedShellMultiplicity A r := by
  classical
  unfold SparseShell at hnot
  exact Nat.not_le.mp (by intro hle; exact hnot ⟨hr, hle⟩)

/-- The distance shells partition the ordered pair-event budget. -/
theorem sum_orderedShellMultiplicity_eq_budget (A : Finset Point2) :
    (∑ r ∈ orderedDistanceSpectrum A, orderedShellMultiplicity A r) =
      totalOrderedPairBudget A := by
  classical
  let f : Point2 × Point2 → ℝ := fun pq => dist pq.1 pq.2
  have hMaps :
      Set.MapsTo f ↑(orderedPairEvents A) ↑(orderedDistanceSpectrum A) := by
    intro pq hpq
    unfold orderedDistanceSpectrum
    exact Finset.mem_image.mpr ⟨pq, hpq, rfl⟩
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := orderedPairEvents A)
      (t := orderedDistanceSpectrum A)
      (f := f) hMaps
  simpa [orderedShellMultiplicity, totalOrderedPairBudget, f] using h.symm

/-- There is a second sparse shell after the diameter shell is removed. -/
def ExistsSecondSparseShell (A : Finset Point2) (Δ : ℝ) : Prop :=
  ∃ r : ℝ, r ≠ Δ ∧ SparseShell A r

/-- A surviving deep-layer case: no non-diameter occupied shell has yet been
shown sparse.  The later geometry bridge must rule these cases out. -/
structure DeepLayerCase (A : Finset Point2) (Δ : ℝ) : Prop where
  no_second_sparse :
    ∀ r : ℝ, r ∈ orderedDistanceSpectrum A → r ≠ Δ → ¬ SparseShell A r

/-- In a deep-layer case, every occupied non-diameter shell is supercritical. -/
theorem DeepLayerCase.supercritical
    {A : Finset Point2} {Δ r : ℝ}
    (h : DeepLayerCase A Δ)
    (hr : r ∈ orderedDistanceSpectrum A)
    (hr_ne : r ≠ Δ) :
    2 * A.card < orderedShellMultiplicity A r :=
  orderedShellMultiplicity_supercritical_of_not_sparse hr
    (h.no_second_sparse r hr hr_ne)

/-- Non-diameter occupied shells in a deep-layer case consume at least
`2|A|+1` ordered events each.  This is the checked finite-counting pressure
behind the low-shell regime in the proof plan. -/
theorem non_diameter_shell_count_pressure
    {A : Finset Point2} {Δ : ℝ}
    (hDeep : DeepLayerCase A Δ) :
    (((orderedDistanceSpectrum A).filter (fun r => r ≠ Δ)).card) *
        (2 * A.card + 1) ≤ totalOrderedPairBudget A := by
  classical
  let S := (orderedDistanceSpectrum A).filter (fun r => r ≠ Δ)
  have h_each :
      ∀ r ∈ S, 2 * A.card + 1 ≤ orderedShellMultiplicity A r := by
    intro r hrS
    have hr : r ∈ orderedDistanceSpectrum A := by
      exact (Finset.mem_filter.mp hrS).1
    have hr_ne : r ≠ Δ := by
      exact (Finset.mem_filter.mp hrS).2
    exact Nat.succ_le_of_lt (hDeep.supercritical hr hr_ne)
  calc
    S.card * (2 * A.card + 1)
        = ∑ r ∈ S, (2 * A.card + 1) := by
            simp [Finset.sum_const]
    _ ≤ ∑ r ∈ S, orderedShellMultiplicity A r := by
            exact Finset.sum_le_sum h_each
    _ ≤ ∑ r ∈ orderedDistanceSpectrum A, orderedShellMultiplicity A r := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (by
                intro r hr
                exact (Finset.mem_filter.mp hr).1)
              (by
                intro r _ _
                exact Nat.zero_le _)
    _ = totalOrderedPairBudget A := sum_orderedShellMultiplicity_eq_budget A

/-- Arithmetic core of pair-budget pressure: if `k` classes each consume at
least `2n+1` ordered events inside an `n^2` budget, then `k ≤ n/2`. -/
theorem shell_pressure_arithmetic
    (k n : ℕ) (h : k * (2 * n + 1) ≤ n * n) :
    k ≤ n / 2 := by
  by_cases hn : n = 0
  · subst hn
    simp at h
    exact le_of_eq h
  by_contra hknot
  have hkgt : n / 2 < k := Nat.lt_of_not_ge hknot
  have hkle : n / 2 + 1 ≤ k := Nat.succ_le_of_lt hkgt
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlt2 : n < 2 * (n / 2 + 1) := by omega
  have hltmul : n * n < (2 * (n / 2 + 1)) * n := by
    exact Nat.mul_lt_mul_of_pos_right hlt2 hpos
  have hle_rearr :
      (2 * (n / 2 + 1)) * n ≤ (n / 2 + 1) * (2 * n + 1) := by
    nlinarith
  have hstrict : n * n < (n / 2 + 1) * (2 * n + 1) :=
    lt_of_lt_of_le hltmul hle_rearr
  have hle2 :
      (n / 2 + 1) * (2 * n + 1) ≤ k * (2 * n + 1) :=
    Nat.mul_le_mul_right _ hkle
  have hcontr : n * n < k * (2 * n + 1) := lt_of_lt_of_le hstrict hle2
  exact (not_lt_of_ge h) hcontr

/-- If the diameter shell is occupied, the occupied shell count is at most the
number of non-diameter shells plus one. -/
theorem occupiedShellCount_le_nonDiameter_add_one
    {A : Finset Point2} {Δ : ℝ}
    (hΔmem : Δ ∈ orderedDistanceSpectrum A) :
    occupiedShellCount A ≤
      ((orderedDistanceSpectrum A).filter (fun r => r ≠ Δ)).card + 1 := by
  classical
  unfold occupiedShellCount
  have hEq :
      ((orderedDistanceSpectrum A).filter (fun r => r ≠ Δ)).card + 1 =
        (orderedDistanceSpectrum A).card := by
    rw [Finset.filter_ne']
    exact Finset.card_erase_add_one hΔmem
  omega

/-- Pair-budget pressure: if no second sparse shell has been found, then the
number of occupied shells is forced into the low-shell regime. -/
structure PairBudgetPressure (A : Finset Point2) (Δ : ℝ) : Prop where
  few_shells_if_deep :
    DeepLayerCase A Δ → occupiedShellCount A ≤ A.card / 2 + 2

/-- The pair-budget component of the final plan is pure finite accounting:
in a deep-layer residual case, all non-diameter shells are supercritical, so
there can be at most `|A|/2` of them, and hence at most `|A|/2 + 1` occupied
shells. -/
theorem pair_budget_pressure_from_counting
    (A : Finset Point2) (Δ : ℝ)
    (hΔ : IsDiameterShell A Δ) :
    PairBudgetPressure A Δ where
  few_shells_if_deep := by
    intro hDeep
    let S := (orderedDistanceSpectrum A).filter (fun r => r ≠ Δ)
    have hPressure :
        S.card * (2 * A.card + 1) ≤ totalOrderedPairBudget A := by
      simpa [S] using non_diameter_shell_count_pressure (A := A) (Δ := Δ) hDeep
    have hBudget : totalOrderedPairBudget A ≤ A.card * A.card :=
      totalOrderedPairBudget_le_all_pairs A
    have hCombined : S.card * (2 * A.card + 1) ≤ A.card * A.card :=
      le_trans hPressure hBudget
    have hS : S.card ≤ A.card / 2 :=
      shell_pressure_arithmetic S.card A.card hCombined
    have hOcc :
        occupiedShellCount A ≤ S.card + 1 := by
      simpa [S] using occupiedShellCount_le_nonDiameter_add_one
        (A := A) (Δ := Δ) hΔ.1
    omega

/-- Low-shell structure: the configuration has entered the small radial
spectrum regime where convex-layer analysis must take over. -/
structure LowShellStructure (A : Finset Point2) (Δ : ℝ) : Prop where
  few_shells : occupiedShellCount A ≤ A.card / 2 + 2

/-- Layer-flux alternative: once in the low-shell regime, either the desired
second sparse shell is present, or the only remaining obstruction is a
deep-layer case. -/
structure LayerFluxAlternative (A : Finset Point2) (Δ : ℝ) : Prop where
  exits_or_deep : ExistsSecondSparseShell A Δ ∨ DeepLayerCase A Δ

/-- The layer-flux alternative is a tautological split at the level of the
current definitions: either a second sparse shell exists, or we are in the
residual deep-layer case.  The hard geometry is therefore not this split, but
screening the residual case. -/
theorem layer_flux_alternative_of_definitions
    (A : Finset Point2) (Δ : ℝ) :
    LayerFluxAlternative A Δ := by
  classical
  by_cases h : ExistsSecondSparseShell A Δ
  · exact ⟨Or.inl h⟩
  · refine ⟨Or.inr ?_⟩
    refine ⟨?_⟩
    intro r hr hr_ne hsparse
    exact h ⟨r, hr_ne, hsparse⟩

/-- Deep-layer screening: the residual deep-layer cases cannot persist. -/
structure DeepLayerScreening (A : Finset Point2) (Δ : ℝ) : Prop where
  screen : DeepLayerCase A Δ → ExistsSecondSparseShell A Δ

/-- The component package specified by the proof plan.  Each field is a
standalone classical bridge target; together they close the shell-flux bridge.
-/
structure ShellFluxComponentPack : Prop where
  pair_budget_pressure :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ, IsDiameterShell A Δ → PairBudgetPressure A Δ
  low_shell_structure :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              PairBudgetPressure A Δ → LowShellStructure A Δ
  layer_flux_alternative :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              LowShellStructure A Δ → LayerFluxAlternative A Δ
  deep_layer_screening :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              LowShellStructure A Δ → DeepLayerScreening A Δ

/-- Reduced component package after observing that `LayerFluxAlternative` is
just the definitional split "exit or residual case".  This is the sharper
implementation target for the remaining proof. -/
structure ShellFluxReducedComponentPack : Prop where
  low_shell_structure :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              PairBudgetPressure A Δ → LowShellStructure A Δ
  deep_layer_screening :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              LowShellStructure A Δ → DeepLayerScreening A Δ

/-- The reduced package supplies the full component package by the definitional
layer-flux split. -/
theorem shell_flux_component_pack_of_reduced
    (C : ShellFluxReducedComponentPack) :
    ShellFluxComponentPack where
  pair_budget_pressure := by
    filter_upwards with n
    intro A _ Δ hΔ
    exact pair_budget_pressure_from_counting A Δ hΔ
  low_shell_structure := C.low_shell_structure
  layer_flux_alternative := by
    filter_upwards with n
    intro A _ Δ _ _
    exact layer_flux_alternative_of_definitions A Δ
  deep_layer_screening := C.deep_layer_screening

/-- The component package closes the missing shell-flux bridge. -/
theorem second_sparse_shell_flux_bridge_from_components
    (C : ShellFluxComponentPack) :
    SecondSparseShellFluxBridge := by
  filter_upwards
    [C.pair_budget_pressure,
     C.low_shell_structure,
     C.layer_flux_alternative,
     C.deep_layer_screening]
    with n hBudget hLow hLayer hScreen
  intro A hA Δ hΔ
  have hBudgetA : PairBudgetPressure A Δ := hBudget A hA Δ hΔ
  have hLowA : LowShellStructure A Δ := hLow A hA Δ hΔ hBudgetA
  have hLayerA : LayerFluxAlternative A Δ := hLayer A hA Δ hΔ hLowA
  have hScreenA : DeepLayerScreening A Δ := hScreen A hA Δ hΔ hLowA
  rcases hLayerA.exits_or_deep with hExit | hDeep
  · exact hExit
  · exact hScreenA.screen hDeep

/-- Hopf-Pannwitz plus the component package proves the ordered form of
Erdős #132.  This is the executable proof graph from the HTML plan. -/
theorem erdos132_from_hopf_pannwitz_and_components
    (hHP : HopfPannwitzOrderedDiameterBound)
    (C : ShellFluxComponentPack) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_flux hHP
    (second_sparse_shell_flux_bridge_from_components C)

/-- Final assembly from the sharper reduced component package. -/
theorem erdos132_from_hopf_pannwitz_and_reduced_components
    (hHP : HopfPannwitzOrderedDiameterBound)
    (C : ShellFluxReducedComponentPack) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_components hHP
    (shell_flux_component_pack_of_reduced C)

/-- Minimal remaining geometry package after implementing the finite
pair-budget pressure.  The only nontrivial geometric work left is screening
the residual deep-layer case once its low-shell bound has been obtained from
finite counting. -/
structure ShellFluxMinimalGeometryPack : Prop where
  deep_layer_screening :
    ∀ᶠ n in atTop,
      ∀ A : Finset Point2,
        A.card = n →
          ∀ Δ : ℝ,
            IsDiameterShell A Δ →
              LowShellStructure A Δ → DeepLayerScreening A Δ

/-- Exact final contradiction target: in the low-shell regime, the residual
deep-layer case cannot occur.  This is the sharp geometric theorem left by the
finite accounting reductions. -/
def NoDeepLayerCaseInLowShellRegime : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            LowShellStructure A Δ →
              ¬ DeepLayerCase A Δ

/-- Pointwise form of the low-shell no-deep-layer theorem.  The Erdős #132
target only needs the eventual version, but this is the cleaner classical
geometric statement when small finite exceptions are not needed. -/
def PointwiseNoDeepLayerCaseInLowShellRegime : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        LowShellStructure A Δ →
          ¬ DeepLayerCase A Δ

/-- Pointwise positive screening form of the layer residual.  This matches the
proof plan's Deep-Layer Screening Lemma: under the low-shell hypotheses, any
residual deep-layer case produces the missing second sparse shell. -/
def PointwiseDeepLayerScreeningCertificate : Prop :=
  ∀ A : Finset Point2,
    ∀ Δ : ℝ,
      IsDiameterShell A Δ →
        LowShellStructure A Δ →
          DeepLayerScreening A Δ

/-- Positive deep-layer screening rules out the residual deep-layer case,
because `DeepLayerCase` definitionally says no second sparse shell exists. -/
theorem pointwise_no_deep_layer_from_screening_certificate
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    PointwiseNoDeepLayerCaseInLowShellRegime := by
  intro A Δ hΔ hLow hDeep
  rcases (hScreen A Δ hΔ hLow).screen hDeep with ⟨r, hr_ne, hsparse⟩
  exact hDeep.no_second_sparse r hsparse.1 hr_ne hsparse

/-- Conversely, pointwise no-deep-layer contradiction supplies the positive
screening certificate, by contradiction.  Hence the residual can be stated in
either positive or negative form without changing mathematical content. -/
theorem pointwise_screening_certificate_from_no_deep_layer
    (hNoDeep : PointwiseNoDeepLayerCaseInLowShellRegime) :
    PointwiseDeepLayerScreeningCertificate := by
  intro A Δ hΔ hLow
  refine ⟨?_⟩
  intro hDeep
  exact False.elim (hNoDeep A Δ hΔ hLow hDeep)

/-- The pointwise positive and negative layer residuals are equivalent. -/
theorem pointwise_deep_layer_screening_iff_no_deep_layer :
    PointwiseDeepLayerScreeningCertificate ↔
      PointwiseNoDeepLayerCaseInLowShellRegime :=
  ⟨pointwise_no_deep_layer_from_screening_certificate,
    pointwise_screening_certificate_from_no_deep_layer⟩

/-- The pointwise no-deep-layer theorem implies the eventual theorem used in the
Erdős #132 assembly. -/
theorem no_deep_layer_from_pointwise
    (h : PointwiseNoDeepLayerCaseInLowShellRegime) :
    NoDeepLayerCaseInLowShellRegime := by
  filter_upwards with n
  intro A _hA Δ hΔ hLow
  exact h A Δ hΔ hLow

/-- Pointwise positive screening supplies the eventual no-deep theorem used by
the Erdős #132 assembly. -/
theorem no_deep_layer_from_pointwise_screening_certificate
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    NoDeepLayerCaseInLowShellRegime :=
  no_deep_layer_from_pointwise
    (pointwise_no_deep_layer_from_screening_certificate hScreen)

/-- Abstract first/second convex-layer package for a finite planar set.  This
is intentionally structural: the detailed geometric construction of layers can
be supplied later, while the final shell-flux proof already knows exactly what
properties it needs. -/
structure ConvexLayerData (A : Finset Point2) where
  L1 : Finset Point2
  L2 : Finset Point2
  L1_subset : L1 ⊆ A
  L2_subset : L2 ⊆ A

/-- A layer package is strong enough to screen the residual deep-layer case for
one chosen diameter shell.  This is the local form of the Clemen-Dumitrescu-Liu
style convex-layer bridge in the plan. -/
def ConvexLayerScreensDeepCase
    (A : Finset Point2) (Δ : ℝ) (_L : ConvexLayerData A) : Prop :=
  LowShellStructure A Δ → ¬ DeepLayerCase A Δ

/-- Global convex-layer screening theorem: every sufficiently large finite set
admits first/second layer data that screens the low-shell residual deep-layer
case.  This is the exact remaining layer-flux theorem named by the plan. -/
def ConvexLayerScreeningBridge : Prop :=
  ∀ᶠ n in atTop,
    ∀ A : Finset Point2,
      A.card = n →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∃ L : ConvexLayerData A, ConvexLayerScreensDeepCase A Δ L

/-- Thresholded form of convex-layer screening.  This is the most concrete
statement of the remaining layer theorem: exhibit a finite `N` such that every
configuration with at least `N` points has first/second layer data screening the
low-shell residual deep-layer case. -/
def ConvexLayerScreeningThresholdCertificate : Prop :=
  ∃ N : ℕ,
    ∀ A : Finset Point2,
      N ≤ A.card →
        ∀ Δ : ℝ,
          IsDiameterShell A Δ →
            ∃ L : ConvexLayerData A, ConvexLayerScreensDeepCase A Δ L

/-- A thresholded convex-layer certificate gives the eventual bridge. -/
theorem convex_layer_screening_from_threshold
    (h : ConvexLayerScreeningThresholdCertificate) :
    ConvexLayerScreeningBridge := by
  rcases h with ⟨N, hN⟩
  unfold ConvexLayerScreeningBridge
  rw [Filter.eventually_atTop]
  refine ⟨N, ?_⟩
  intro n hn A hA Δ hΔ
  exact hN A (by rw [hA]; exact hn) Δ hΔ

/-- Conversely, the eventual bridge supplies some threshold. -/
theorem convex_layer_screening_threshold_from_bridge
    (h : ConvexLayerScreeningBridge) :
    ConvexLayerScreeningThresholdCertificate := by
  unfold ConvexLayerScreeningBridge at h
  rw [Filter.eventually_atTop] at h
  rcases h with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro A hA Δ hΔ
  exact hN A.card hA A rfl Δ hΔ

/-- The eventual and thresholded convex-layer formulations are equivalent. -/
theorem convex_layer_screening_iff_threshold :
    ConvexLayerScreeningBridge ↔ ConvexLayerScreeningThresholdCertificate :=
  ⟨convex_layer_screening_threshold_from_bridge,
    convex_layer_screening_from_threshold⟩

/-- The convex-layer screening bridge implies the no-deep-layer target. -/
theorem no_deep_layer_from_convex_layer_screening
    (hLayer : ConvexLayerScreeningBridge) :
    NoDeepLayerCaseInLowShellRegime := by
  filter_upwards [hLayer] with n hLayerN
  intro A hA Δ hΔ hLow
  rcases hLayerN A hA Δ hΔ with ⟨L, hScreen⟩
  exact hScreen hLow

/-- Conversely, the no-deep-layer target supplies the current structural
convex-layer bridge.  The `ConvexLayerData` fields are only bookkeeping here;
the mathematical content is exactly `NoDeepLayerCaseInLowShellRegime`.  This
keeps the final residual honest: the remaining layer theorem is the
low-shell/no-deep contradiction itself, not the choice of layer containers. -/
theorem convex_layer_screening_from_no_deep_layer
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    ConvexLayerScreeningBridge := by
  filter_upwards [hNoDeep] with n hNoDeepN
  intro A hA Δ hΔ
  refine ⟨{ L1 := ∅, L2 := ∅, L1_subset := ?_, L2_subset := ?_ }, ?_⟩
  · intro x hx
    simp at hx
  · intro x hx
    simp at hx
  · intro hLow hDeep
    exact hNoDeepN A hA Δ hΔ hLow hDeep

/-- The structural convex-layer bridge is equivalent to the sharper low-shell
no-deep-layer target. -/
theorem convex_layer_screening_iff_no_deep_layer :
    ConvexLayerScreeningBridge ↔ NoDeepLayerCaseInLowShellRegime :=
  ⟨no_deep_layer_from_convex_layer_screening,
    convex_layer_screening_from_no_deep_layer⟩

/-- The no-deep-layer contradiction target is exactly enough to screen the
residual case. -/
theorem minimal_geometry_pack_of_no_deep_layer
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    ShellFluxMinimalGeometryPack where
  deep_layer_screening := by
    filter_upwards [hNoDeep] with n hNoDeepN
    intro A hA Δ hΔ hLow
    refine ⟨?_⟩
    intro hDeep
    exact False.elim (hNoDeepN A hA Δ hΔ hLow hDeep)

/-- The minimal geometry package closes the shell-flux bridge.  The proof
splits definitionally into "a second sparse shell already exists" or "we are
in the residual deep-layer case"; in the residual case, finite pair-budget
pressure supplies the low-shell hypothesis needed by screening. -/
theorem second_sparse_shell_flux_bridge_from_minimal_geometry
    (G : ShellFluxMinimalGeometryPack) :
    SecondSparseShellFluxBridge := by
  filter_upwards [G.deep_layer_screening] with n hScreen
  intro A hA Δ hΔ
  by_cases hExit : ExistsSecondSparseShell A Δ
  · exact hExit
  · have hDeep : DeepLayerCase A Δ := by
      refine ⟨?_⟩
      intro r hr hr_ne hsparse
      exact hExit ⟨r, hr_ne, hsparse⟩
    have hBudget : PairBudgetPressure A Δ :=
      pair_budget_pressure_from_counting A Δ hΔ
    have hLow : LowShellStructure A Δ :=
      ⟨PairBudgetPressure.few_shells_if_deep hBudget hDeep⟩
    have hScreenA : DeepLayerScreening A Δ := hScreen A hA Δ hΔ hLow
    exact hScreenA.screen hDeep

/-- Hopf-Pannwitz plus the single remaining deep-layer screening bridge proves
Erdős #132 in ordered-pair normalization. -/
theorem erdos132_from_hopf_pannwitz_and_minimal_geometry
    (hHP : HopfPannwitzOrderedDiameterBound)
    (G : ShellFluxMinimalGeometryPack) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_flux hHP
    (second_sparse_shell_flux_bridge_from_minimal_geometry G)

/-- Hopf-Pannwitz plus the exact no-deep-layer theorem proves Erdős #132.
This is the current sharp final assembly theorem: all finite counting has been
implemented, so the only remaining input is the geometric impossibility of the
low-shell residual case. -/
theorem erdos132_from_hopf_pannwitz_and_no_deep_layer
    (hHP : HopfPannwitzOrderedDiameterBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_minimal_geometry hHP
    (minimal_geometry_pack_of_no_deep_layer hNoDeep)

/-- Fully reduced final assembly theorem after implementing the proof-plan
bookkeeping.  The remaining classical geometry inputs are exactly:

1. diameter shell existence,
2. Hopf-Pannwitz diameter sparsity,
3. no residual deep-layer case in the low-shell regime.
-/
theorem erdos132_from_final_components
    (H : HopfPannwitzComponentPack)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_no_deep_layer
    (hopf_pannwitz_ordered_from_components H)
    hNoDeep

/-- Diameter-sparsity assembly: diameter existence and finite bookkeeping are
proved, so this conditional theorem packages the older Hopf-Pannwitz sparsity
surface with the low-shell no-deep theorem.  The current live endpoint is
`Erdos132CurrentLiveResidual`. -/
theorem erdos132_from_diameter_sparsity_and_no_deep_layer
    (hSparse : DiameterShellSparseBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_hopf_pannwitz_and_no_deep_layer
    (hopf_pannwitz_ordered_from_diameter_sparsity hSparse)
    hNoDeep

/-- Final assembly from the thrackle-level Hopf-Pannwitz components plus the
low-shell no-deep-layer theorem. -/
theorem erdos132_from_thrackle_and_no_deep_layer
    (hNoDisjoint : NoDisjointDiameterEdges)
    (hThrackle : OrderedThrackleBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_diameter_sparsity_and_no_deep_layer
    (diameter_shell_sparse_from_thrackle_components hNoDisjoint hThrackle)
    hNoDeep

/-- Legacy assembly from the older set-theoretic undirected thrackle
decomposition.  This is kept as a conditional theorem, but the predicate
`UndirectedThrackleSupportBound` is too strong for arbitrary collinear edge
systems.  Use the live Conway endpoint
`erdos132_from_ordered_conway_convex_layer_residual_pack` for the corrected
proof graph. -/
theorem erdos132_from_undirected_thrackle_and_no_deep_layer
    (hNoDisjoint : NoDisjointDiameterEdges)
    (hSupport : UndirectedThrackleSupportBound)
    (hOrient : OrderedOrientationFiberBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_thrackle_and_no_deep_layer hNoDisjoint
    (ordered_thrackle_bound_from_undirected_support hSupport hOrient)
    hNoDeep

/-- Legacy assembly through the deprecated set-theoretic undirected support
bound.  Orientation bookkeeping is proved, but the support predicate is not the
correct Conway thrackle theorem. -/
theorem erdos132_from_undirected_thrackle_support_and_no_deep_layer
    (hNoDisjoint : NoDisjointDiameterEdges)
    (hSupport : UndirectedThrackleSupportBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_thrackle_and_no_deep_layer hNoDisjoint
    (ordered_thrackle_bound_from_undirected_support_only hSupport)
    hNoDeep

/-- Legacy assembly through local diameter meeting and the deprecated
set-theoretic undirected support bound. -/
theorem erdos132_from_local_diameter_meeting_thrackle_and_no_deep_layer
    (hMeet : DiameterSegmentsMeetLocally)
    (hSupport : UndirectedThrackleSupportBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_undirected_thrackle_support_and_no_deep_layer
    (no_disjoint_diameter_edges_from_local_meeting hMeet)
    hSupport
    hNoDeep

/-- Legacy assembly from the endpoint-disjoint local diameter geometry core and
the deprecated set-theoretic undirected support bound. -/
theorem erdos132_from_endpoint_disjoint_diameter_core_thrackle_and_no_deep_layer
    (hCore : EndpointDisjointDiameterSegmentsMeetLocally)
    (hSupport : UndirectedThrackleSupportBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_local_diameter_meeting_thrackle_and_no_deep_layer
    (diameter_segments_meet_from_endpoint_disjoint_core hCore)
    hSupport
    hNoDeep

/-- Legacy four-point assembly through the deprecated set-theoretic undirected
support bound.  The four-point diameter geometry is live and proved; the
correct counting input is the Conway theorem used in the final endpoint below. -/
theorem erdos132_from_four_point_thrackle_and_no_deep_layer
    (h4 : FourPointDiameterCrossing)
    (hSupport : UndirectedThrackleSupportBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_endpoint_disjoint_diameter_core_thrackle_and_no_deep_layer
    (endpoint_disjoint_local_meeting_from_four_point h4)
    hSupport
    hNoDeep

/-- Legacy plan-language assembly before the Conway correction.  It uses
`UndirectedThrackleSupportBound`, which permits overlapping collinear segments
and is not the correct global counting theorem. -/
theorem erdos132_from_four_point_thrackle_and_convex_layer_screening
    (h4 : FourPointDiameterCrossing)
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_four_point_thrackle_and_no_deep_layer h4 hSupport
    (no_deep_layer_from_convex_layer_screening hLayer)

/-- Final assembly from the separated-segment bridge decomposition, undirected
thrackle support, and convex-layer screening. -/
theorem erdos132_from_separation_thrackle_and_convex_layer_screening
    (hSep : DisjointSegmentsHaveSeparation)
    (hProper : ProperSeparatedDiameterContradiction)
    (hCollinear : CollinearSeparatedDiameterContradiction)
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_four_point_thrackle_and_convex_layer_screening
    (four_point_diameter_crossing_from_separation_bridges hSep hProper hCollinear)
    hSupport
    hLayer

/-- Final assembly using the unified separated-diameter contradiction. -/
theorem erdos132_from_unified_separation_thrackle_and_convex_layer_screening
    (hSep : DisjointSegmentsHaveSeparation)
    (hContr : SeparatedDiameterContradiction)
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_four_point_thrackle_and_convex_layer_screening
    (four_point_diameter_crossing_from_separated_diameter hSep hContr)
    hSupport
    hLayer

/-- **Reduced assembly.**  Because `CollinearSeparatedDiameterContradiction`
is now a Lean theorem (`collinearSeparatedDiameterContradiction`), the
collinear case is discharged automatically.  Erdős #132 follows from just the
proper separated-diameter contradiction together with the segment-separation
case split, the undirected thrackle support bound, and convex-layer
screening. -/
theorem erdos132_from_proper_separation_thrackle_and_convex_layer_screening
    (hSep : DisjointSegmentsHaveSeparation)
    (hProper : ProperSeparatedDiameterContradiction)
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_separation_thrackle_and_convex_layer_screening
    hSep hProper collinearSeparatedDiameterContradiction
    hSupport hLayer

/-- **Further-reduced assembly.**  Because both
`CollinearSeparatedDiameterContradiction` and
`ProperSeparatedDiameterContradiction` are now Lean theorems
(`collinearSeparatedDiameterContradiction`,
`properSeparatedDiameterContradiction`), the four-point Hopf-Pannwitz lemma is
fully discharged. Erdős #132 follows from just the segment-separation case
split, undirected thrackle support, and convex-layer screening. -/
theorem erdos132_from_separation_thrackle_layer
    (hSep : DisjointSegmentsHaveSeparation)
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_proper_separation_thrackle_and_convex_layer_screening
    hSep properSeparatedDiameterContradiction hSupport hLayer

/-- If `c` lies on the line through `a` and `b` and is in the closed lens
`D(a, Δ) ∩ D(b, Δ)` with `dist a b = Δ`, then `c` is on the closed segment
from `a` to `b`. -/
theorem onClosedSegment_of_orient2_zero_in_lens
    {a b c : Point2} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (hab : dist a b = Δ)
    (hac : dist a c ≤ Δ) (hbc : dist b c ≤ Δ)
    (h_orient : orient2 a b c = 0) :
    OnClosedSegment a b c := by
  have h_ab : a ≠ b := by
    intro he
    rw [he, dist_self] at hab
    linarith
  obtain ⟨t, ht⟩ := exists_scalar_of_orient2_zero h_ab h_orient
  have hac_eq : dist a c = |t| * Δ := by
    have := dist_from_diff_eq_smul ht
    rw [hab] at this
    exact this
  have hbc_param : ∀ i : Fin 2, c i - b i = (t - 1) * (b i - a i) := by
    intro i
    have := ht i
    linarith
  have hbc_eq : dist b c = |t - 1| * Δ := by
    have := dist_from_diff_eq_smul hbc_param
    rw [hab] at this
    exact this
  have habst : |t| ≤ 1 := by
    have h1 : |t| * Δ ≤ 1 * Δ := by
      rw [one_mul]
      linarith [hac_eq ▸ hac]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have habs1mt : |t - 1| ≤ 1 := by
    have h1 : |t - 1| * Δ ≤ 1 * Δ := by
      rw [one_mul]
      linarith [hbc_eq ▸ hbc]
    exact le_of_mul_le_mul_right h1 hΔ_pos
  have ht_le1 : t ≤ 1 := (abs_le.mp habst).2
  have hneg1mt : -(1:ℝ) ≤ t - 1 := (abs_le.mp habs1mt).1
  have ht_nn : 0 ≤ t := by linarith
  refine ⟨t, ht_nn, ht_le1, ?_⟩
  ext i
  have h := ht i
  show c i = ((1 - t) • a + t • b) i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  linarith

/-- If `c` lies on line `ab` and is in the diameter lens, then the segment
`[a,b]` meets `[c,d]` at `c`. -/
theorem segments_meet_of_orient2_zero
    {a b c d : Point2} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (hab : dist a b = Δ)
    (hac : dist a c ≤ Δ) (hbc : dist b c ≤ Δ)
    (h_orient : orient2 a b c = 0) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) := by
  refine ⟨c, ?_, left_endpoint_on_segment c d⟩
  exact onClosedSegment_of_orient2_zero_in_lens hΔ_pos hab hac hbc h_orient

/-- Two distinct diameter representatives sharing their left endpoint meet
simply at that endpoint.  A second intersection point would force the two
other endpoints to lie on the same diameter segment, hence coincide. -/
theorem shared_left_diameter_representatives_meet_simply
    {a b c : Point2} {Δ : ℝ}
    (hUne : unorderedEdgeOfOrdered (a, b) ≠ unorderedEdgeOfOrdered (a, c))
    (hab : dist a b = Δ) (hac : dist a c = Δ) (hbc : dist b c ≤ Δ) :
    OrderedEdgesMeetSimply (a, b) (a, c) := by
  have h_ab : a ≠ b := by
    intro h
    have hΔ0 : Δ = 0 := by
      rw [h, dist_self] at hab
      exact hab.symm
    have hac0 : dist a c = 0 := by rw [hac, hΔ0]
    have hca : c = a := (eq_of_dist_eq_zero hac0).symm
    apply hUne
    rw [h, hca, h]
  have hΔ_pos : 0 < Δ := by
    have hnn : 0 ≤ Δ := hab ▸ dist_nonneg
    have hne : Δ ≠ 0 := by
      intro hΔ0
      have hd : dist a b = 0 := by rw [hab, hΔ0]
      exact h_ab (eq_of_dist_eq_zero hd)
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  refine ⟨a, ⟨left_endpoint_on_segment a b, left_endpoint_on_segment a c⟩, ?_⟩
  intro y hy
  by_contra hya
  have hay : a ≠ y := by exact fun h => hya h.symm
  have h_ab_y : orient2 a b y = 0 := orient2_eq_zero_of_on_closed_segment hy.1
  have h_ac_y : orient2 a c y = 0 := orient2_eq_zero_of_on_closed_segment hy.2
  have h_ayb : orient2 a y b = 0 := by
    rw [orient2_swap₂₃]
    simp [h_ab_y]
  have h_ayc : orient2 a y c = 0 := by
    rw [orient2_swap₂₃]
    simp [h_ac_y]
  have h_abc : orient2 a b c = 0 :=
    orient2_zero_transitive hay h_ayb h_ayc
  have hc_on_ab : OnClosedSegment a b c :=
    onClosedSegment_of_orient2_zero_in_lens hΔ_pos hab (by rw [hac]) hbc h_abc
  have hcb : c = b := by
    apply eq_right_of_on_closed_segment_of_dist_left_eq hc_on_ab
    rw [hac, hab]
  apply hUne
  rw [hcb]

/-- Shared-endpoint diameter representatives of distinct unordered diameter
support edges meet simply.  This discharges the endpoint-sharing half of the
diameter-support Conway condition. -/
theorem shared_endpoint_diameter_representatives_meet_simply :
    SharedEndpointDiameterRepresentativesMeetSimply := by
  intro A Δ hΔ e he f hf hUne hShare
  cases e with
  | mk a b =>
  cases f with
  | mk c d =>
  rcases diameter_ordered_edges_cross_distances_le hΔ he hf with
    ⟨hab, hcd, hac, had, hbc, hbd⟩
  unfold OrderedEdgesShareEndpoint at hShare
  simp at hShare hab hcd hac had hbc hbd
  rcases hShare with h_ac | h_ad | h_bc | h_bd
  · subst c
    exact shared_left_diameter_representatives_meet_simply hUne hab hcd hbd
  · subst d
    have hUne' :
        unorderedEdgeOfOrdered (a, b) ≠ unorderedEdgeOfOrdered (a, c) := by
      intro hEq
      apply hUne
      have hswap : unorderedEdgeOfOrdered (c, a) = unorderedEdgeOfOrdered (a, c) := by
        simpa using unorderedEdgeOfOrdered_swap (a, c)
      exact hEq.trans hswap.symm
    have hsimple :
        OrderedEdgesMeetSimply (a, b) (a, c) :=
      shared_left_diameter_representatives_meet_simply
        hUne' hab (by simpa [dist_comm] using hcd) hbc
    exact ordered_edges_meet_simply_swap_right hsimple
  · subst c
    have hUne' :
        unorderedEdgeOfOrdered (b, a) ≠ unorderedEdgeOfOrdered (b, d) := by
      intro hEq
      apply hUne
      have hswap : unorderedEdgeOfOrdered (b, a) = unorderedEdgeOfOrdered (a, b) := by
        simpa using unorderedEdgeOfOrdered_swap (a, b)
      exact hswap.symm.trans hEq
    have hsimple :
        OrderedEdgesMeetSimply (b, a) (b, d) :=
      shared_left_diameter_representatives_meet_simply
        hUne' (by simpa [dist_comm] using hab) hcd had
    exact ordered_edges_meet_simply_swap_left hsimple
  · subst d
    have hUne' :
        unorderedEdgeOfOrdered (b, a) ≠ unorderedEdgeOfOrdered (b, c) := by
      intro hEq
      apply hUne
      have hswap_e : unorderedEdgeOfOrdered (b, a) = unorderedEdgeOfOrdered (a, b) := by
        simpa using unorderedEdgeOfOrdered_swap (a, b)
      have hswap_f : unorderedEdgeOfOrdered (c, b) = unorderedEdgeOfOrdered (b, c) := by
        simpa using unorderedEdgeOfOrdered_swap (b, c)
      exact hswap_e.symm.trans (hEq.trans hswap_f.symm)
    have hsimple :
        OrderedEdgesMeetSimply (b, a) (b, c) :=
      shared_left_diameter_representatives_meet_simply
        hUne' (by simpa [dist_comm] using hab) (by simpa [dist_comm] using hcd) hac
    exact ordered_edges_meet_simply_swap_right
      (ordered_edges_meet_simply_swap_left hsimple)

/-- A convex combination of two points in a closed ball is in the ball. -/
theorem dist_convex_combination_le
    {a c d : Point2} {Δ : ℝ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hac : dist a c ≤ Δ) (had : dist a d ≤ Δ) :
    dist a ((1 - t) • c + t • d) ≤ Δ := by
  have h_cvx : Convex ℝ (Metric.closedBall a Δ) := convex_closedBall a Δ
  have hc : c ∈ Metric.closedBall a Δ := by
    rw [Metric.mem_closedBall, dist_comm]
    exact hac
  have hd : d ∈ Metric.closedBall a Δ := by
    rw [Metric.mem_closedBall, dist_comm]
    exact had
  have h1mt : 0 ≤ 1 - t := by linarith
  have hsum : (1 - t) + t = 1 := by ring
  have h_in : (1 - t) • c + t • d ∈ Metric.closedBall a Δ :=
    h_cvx hc hd h1mt ht0 hsum
  rw [Metric.mem_closedBall, dist_comm] at h_in
  exact h_in

/-- If `c` and `d` are on opposite strict sides of line `ab`, then under the
diameter cross-distance bounds the segments `[a,b]` and `[c,d]` meet. -/
theorem segments_meet_of_opposite_sides
    {a b c d : Point2} {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (hab : dist a b = Δ)
    (hac : dist a c ≤ Δ) (had : dist a d ≤ Δ)
    (hbc : dist b c ≤ Δ) (hbd : dist b d ≤ Δ)
    (h_opp : orient2 a b c * orient2 a b d < 0) :
    OrderedEdgesMeetGeometrically (a, b) (c, d) := by
  have h_oc_ne : orient2 a b c ≠ 0 := by
    intro h
    rw [h, zero_mul] at h_opp
    linarith
  have h_od_ne : orient2 a b d ≠ 0 := by
    intro h
    rw [h, mul_zero] at h_opp
    linarith
  set u := orient2 a b c
  set v := orient2 a b d
  have huv : u * v < 0 := h_opp
  set t := u / (u - v) with ht_def
  have h_denom_ne : u - v ≠ 0 := by
    intro h
    have : u = v := by linarith
    rw [this] at huv
    have : v * v ≥ 0 := mul_self_nonneg v
    linarith
  have ht_pos : 0 < t := by
    rcases lt_trichotomy u 0 with hu | hu | hu
    · have hv : 0 < v := by
        rcases lt_trichotomy v 0 with h | h | h
        · have : 0 < u * v := mul_pos_of_neg_of_neg hu h
          linarith
        · rw [h] at huv
          linarith
        · exact h
      have hd_neg : u - v < 0 := by linarith
      exact div_pos_of_neg_of_neg hu hd_neg
    · rw [hu] at h_oc_ne
      exact absurd rfl h_oc_ne
    · have hv : v < 0 := by
        rcases lt_trichotomy v 0 with h | h | h
        · exact h
        · rw [h] at huv
          linarith
        · have : 0 < u * v := mul_pos hu h
          linarith
      have hd_pos : 0 < u - v := by linarith
      exact div_pos hu hd_pos
  have ht_lt : t < 1 := by
    have h_t_minus_1 : t - 1 = v / (u - v) := by
      rw [ht_def]
      field_simp
      ring
    rcases lt_trichotomy u 0 with hu | hu | hu
    · have hv : 0 < v := by
        rcases lt_trichotomy v 0 with h | h | h
        · have : 0 < u * v := mul_pos_of_neg_of_neg hu h
          linarith
        · rw [h] at huv
          linarith
        · exact h
      have hd_neg : u - v < 0 := by linarith
      have h_quot_neg : v / (u - v) < 0 := div_neg_of_pos_of_neg hv hd_neg
      linarith [h_t_minus_1, h_quot_neg]
    · rw [hu] at h_oc_ne
      exact absurd rfl h_oc_ne
    · have hv : v < 0 := by
        rcases lt_trichotomy v 0 with h | h | h
        · exact h
        · rw [h] at huv
          linarith
        · have : 0 < u * v := mul_pos hu h
          linarith
      have hd_pos : 0 < u - v := by linarith
      have h_quot_neg : v / (u - v) < 0 := div_neg_of_neg_of_pos hv hd_pos
      linarith [h_t_minus_1, h_quot_neg]
  set P := (1 - t) • c + t • d with hP_def
  have hP_on_cd : OnClosedSegment c d P := ⟨t, le_of_lt ht_pos, le_of_lt ht_lt, rfl⟩
  have h_orient_P : orient2 a b P = 0 := by
    have h_aff : orient2 a b P = (1 - t) * orient2 a b c + t * orient2 a b d := by
      rw [hP_def]
      exact orient2_affine_third a b c d t
    have h_aff' : orient2 a b P = (1 - t) * u + t * v := h_aff
    rw [h_aff', ht_def]
    field_simp
    ring
  have hP_aΔ : dist a P ≤ Δ := by
    exact dist_convex_combination_le t (le_of_lt ht_pos) (le_of_lt ht_lt) hac had
  have hP_bΔ : dist b P ≤ Δ := by
    exact dist_convex_combination_le t (le_of_lt ht_pos) (le_of_lt ht_lt) hbc hbd
  have hP_on_ab : OnClosedSegment a b P :=
    onClosedSegment_of_orient2_zero_in_lens hΔ_pos hab hP_aΔ hP_bΔ h_orient_P
  exact ⟨P, hP_on_ab, hP_on_cd⟩

/-
The following same-side and crossing lemmas close the four-point
Hopf-Pannwitz geometry used by the live final assemblies below.
-/

set_option maxHeartbeats 6400000 in
/-- **Sharper same-side bridge.**  The proof of
`properSeparatedDiameterContradiction` only uses the first orientation
product condition of `ProperSegmentSeparation`, not the second.  This
strengthens it: under the diameter conditions, having `c` and `d` strictly
on the same side of line `ab` (i.e., `orient2 a b c · orient2 a b d > 0`)
already gives a contradiction. -/
theorem sameSideDiameterContradiction
    (a b c d : Point2) (Δ : ℝ)
    (h_ac : a ≠ c) (_h_ad : a ≠ d) (_h_bc : b ≠ c) (_h_bd : b ≠ d)
    (hab : dist a b = Δ) (hcd : dist c d = Δ)
    (hac : dist a c ≤ Δ) (had : dist a d ≤ Δ) (hbc : dist b c ≤ Δ) (hbd : dist b d ≤ Δ)
    (h_same_side : 0 < orient2 a b c * orient2 a b d) :
    False := by
  by_cases hΔ : Δ = 0
  · subst hΔ
    have h : dist a c = 0 := le_antisymm hac dist_nonneg
    exact h_ac (eq_of_dist_eq_zero h)
  have hΔ_nn : 0 ≤ Δ := hab ▸ dist_nonneg
  have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nn (Ne.symm hΔ)
  have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
  have hab_sq : Δ*Δ = (b 0 - a 0)^2 + (b 1 - a 1)^2 := by
    have h := dist_sq_unfold a b
    rw [hab] at h
    nlinarith [h]
  have hac_sq_le : (c 0 - a 0)^2 + (c 1 - a 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold a c
    have hac_nn : 0 ≤ dist a c := dist_nonneg
    have : (dist a c)^2 ≤ Δ^2 := by nlinarith [hac_nn, hac]
    nlinarith [h, this]
  have had_sq_le : (d 0 - a 0)^2 + (d 1 - a 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold a d
    have hd_nn : 0 ≤ dist a d := dist_nonneg
    have : (dist a d)^2 ≤ Δ^2 := by nlinarith [hd_nn, had]
    nlinarith [h, this]
  have hbc_sq_le : (b 0 - c 0)^2 + (b 1 - c 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold b c
    have hd_nn : 0 ≤ dist b c := dist_nonneg
    have : (dist b c)^2 ≤ Δ^2 := by nlinarith [hd_nn, hbc]
    nlinarith [h, this]
  have hbd_sq_le : (b 0 - d 0)^2 + (b 1 - d 1)^2 ≤ Δ*Δ := by
    have h := dist_sq_unfold b d
    have hd_nn : 0 ≤ dist b d := dist_nonneg
    have : (dist b d)^2 ≤ Δ^2 := by nlinarith [hd_nn, hbd]
    nlinarith [h, this]
  have hcd_sq_eq : (c 0 - d 0)^2 + (c 1 - d 1)^2 = Δ*Δ := by
    have h := dist_sq_unfold c d
    rw [hcd] at h
    nlinarith [h]
  have hLag_c : ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1))^2 +
                ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0))^2 =
                ((c 0 - a 0)^2 + (c 1 - a 1)^2) * ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_2d a b c
  have hLag_d : ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1))^2 +
                ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0))^2 =
                ((d 0 - a 0)^2 + (d 1 - a 1)^2) * ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_2d a b d
  have hLag_pol : ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) *
                    ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1)) +
                  ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) *
                    ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0)) =
                  ((c 0 - a 0)*(d 0 - a 0) + (c 1 - a 1)*(d 1 - a 1)) *
                    ((b 0 - a 0)^2 + (b 1 - a 1)^2) :=
    lagrange_identity_polarized_2d a b c d
  set αc := ((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) / Δ with hαc_def
  set βc := ((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) / Δ with hβc_def
  set αd := ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1)) / Δ with hαd_def
  set βd := ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0)) / Δ with hβd_def
  have h_αcβc_eq_ac : αc*αc + βc*βc = (c 0 - a 0)^2 + (c 1 - a 1)^2 := by
    rw [hαc_def, hβc_def]; field_simp; nlinarith [hLag_c, hab_sq]
  have h_αdβd_eq_ad : αd*αd + βd*βd = (d 0 - a 0)^2 + (d 1 - a 1)^2 := by
    rw [hαd_def, hβd_def]; field_simp; nlinarith [hLag_d, hab_sq]
  have h_αcβc_eq_bc : (αc - Δ)*(αc - Δ) + βc*βc = (b 0 - c 0)^2 + (b 1 - c 1)^2 := by
    have e1 : αc * Δ = (c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1) := by
      rw [hαc_def]; field_simp
    have e2 : (αc - Δ)*(αc - Δ) + βc*βc = (αc*αc + βc*βc) - 2*(αc*Δ) + Δ*Δ := by ring
    rw [e2, h_αcβc_eq_ac, e1, hab_sq]; ring
  have h_αdβd_eq_bd : (αd - Δ)*(αd - Δ) + βd*βd = (b 0 - d 0)^2 + (b 1 - d 1)^2 := by
    have e1 : αd * Δ = (d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1) := by
      rw [hαd_def]; field_simp
    have e2 : (αd - Δ)*(αd - Δ) + βd*βd = (αd*αd + βd*βd) - 2*(αd*Δ) + Δ*Δ := by ring
    rw [e2, h_αdβd_eq_ad, e1, hab_sq]; ring
  have h_cd_eq : (αc - αd)*(αc - αd) + (βc - βd)*(βc - βd) = (c 0 - d 0)^2 + (c 1 - d 1)^2 := by
    have e1 : αc * αd + βc * βd = (c 0 - a 0)*(d 0 - a 0) + (c 1 - a 1)*(d 1 - a 1) := by
      have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
      have h1 : αc * αd = (((c 0 - a 0)*(b 0 - a 0) + (c 1 - a 1)*(b 1 - a 1)) *
                          ((d 0 - a 0)*(b 0 - a 0) + (d 1 - a 1)*(b 1 - a 1))) / (Δ*Δ) := by
        rw [hαc_def, hαd_def]; field_simp
      have h2 : βc * βd = (((b 0 - a 0)*(c 1 - a 1) - (b 1 - a 1)*(c 0 - a 0)) *
                          ((b 0 - a 0)*(d 1 - a 1) - (b 1 - a 1)*(d 0 - a 0))) / (Δ*Δ) := by
        rw [hβc_def, hβd_def]; field_simp
      rw [h1, h2, ← add_div]
      rw [hLag_pol, ← hab_sq]
      field_simp
    have e2 : (αc - αd)*(αc - αd) + (βc - βd)*(βc - βd) =
              (αc*αc + βc*βc) + (αd*αd + βd*βd) - 2*(αc*αd + βc*βd) := by ring
    rw [e2, h_αcβc_eq_ac, h_αdβd_eq_ad, e1]
    ring
  have hβc_orient : βc * Δ = orient2 a b c := by
    rw [hβc_def]; field_simp; unfold orient2; ring
  have hβd_orient : βd * Δ = orient2 a b d := by
    rw [hβd_def]; field_simp; unfold orient2; ring
  have hβ_prod : 0 < βc * βd := by
    have : 0 < (βc * Δ) * (βd * Δ) := by
      rw [hβc_orient, hβd_orient]; exact h_same_side
    have hΔΔ_pos : 0 < Δ*Δ := mul_pos hΔ_pos hΔ_pos
    nlinarith [this, hΔΔ_pos]
  have hi_lens : αc*αc + βc*βc ≤ Δ*Δ := by rw [h_αcβc_eq_ac]; exact hac_sq_le
  have hii_lens : (αc - Δ)*(αc - Δ) + βc*βc ≤ Δ*Δ := by rw [h_αcβc_eq_bc]; exact hbc_sq_le
  have hiii_lens : αd*αd + βd*βd ≤ Δ*Δ := by rw [h_αdβd_eq_ad]; exact had_sq_le
  have hiv_lens : (αd - Δ)*(αd - Δ) + βd*βd ≤ Δ*Δ := by rw [h_αdβd_eq_bd]; exact hbd_sq_le
  rcases lt_trichotomy βc 0 with hβc | hβc | hβc
  · have hβd : βd < 0 := by
      by_contra h
      push_neg at h
      rcases lt_or_eq_of_le h with hβd_pos | hβd_zero
      · have : βc * βd < 0 := mul_neg_of_neg_of_pos hβc hβd_pos
        linarith [hβ_prod, this]
      · rw [← hβd_zero] at hβ_prod; linarith
    have hp := hopf_pannwitz_strict_lens_coord_neg Δ αc βc αd βd hΔ_pos
      hi_lens hii_lens hiii_lens hiv_lens hβc hβd
    rw [h_cd_eq] at hp
    linarith [hp, hcd_sq_eq]
  · rw [hβc] at hβ_prod; linarith [hβ_prod]
  · have hβd : 0 < βd := by
      by_contra h
      push_neg at h
      rcases lt_or_eq_of_le h with hβd_neg | hβd_zero
      · have : βc * βd < 0 := mul_neg_of_pos_of_neg hβc hβd_neg
        linarith [hβ_prod, this]
      · rw [hβd_zero] at hβ_prod; linarith
    have hp := hopf_pannwitz_strict_lens_coord Δ αc βc αd βd hΔ_pos
      hi_lens hii_lens hiii_lens hiv_lens hβc hβd
    rw [h_cd_eq] at hp
    linarith [hp, hcd_sq_eq]


/-- **Four-point Hopf-Pannwitz crossing theorem, closed.**  If
`dist a b = dist c d = Δ`, all four cross-distances are at most `Δ`, and the
four endpoints are pairwise distinct across the two segments, then the closed
segments `[a,b]` and `[c,d]` meet geometrically. -/
theorem fourPointDiameterCrossing_thm : FourPointDiameterCrossing := by
  intro a b c d Δ h_ac h_ad h_bc h_bd hab hcd hac had hbc hbd
  by_cases hΔ : Δ = 0
  · subst hΔ
    exact four_point_diameter_crossing_zero_case a b c d h_ac h_ad h_bc h_bd
      hab hcd hac had hbc hbd
  have hΔ_nn : 0 ≤ Δ := hab ▸ dist_nonneg
  have hΔ_pos : 0 < Δ := lt_of_le_of_ne hΔ_nn (Ne.symm hΔ)
  by_contra hnomeet
  have hdisj : OrderedEdgesGeometricallyDisjoint (a, b) (c, d) := hnomeet
  have meet_at_c : orient2 a b c = 0 → OrderedEdgesMeetGeometrically (a, b) (c, d) := by
    intro hc_z
    refine ⟨c,
      onClosedSegment_of_orient2_zero_in_lens hΔ_pos hab hac hbc hc_z,
      left_endpoint_on_segment c d⟩
  have meet_at_d : orient2 a b d = 0 → OrderedEdgesMeetGeometrically (a, b) (c, d) := by
    intro hd_z
    refine ⟨d,
      onClosedSegment_of_orient2_zero_in_lens hΔ_pos hab had hbd hd_z,
      right_endpoint_on_segment c d⟩
  rcases lt_trichotomy (orient2 a b c) 0 with hc_n | hc_z | hc_p
  · rcases lt_trichotomy (orient2 a b d) 0 with hd_n | hd_z | hd_p
    · have hprod : 0 < orient2 a b c * orient2 a b d :=
        mul_pos_of_neg_of_neg hc_n hd_n
      exact sameSideDiameterContradiction a b c d Δ h_ac h_ad h_bc h_bd
        hab hcd hac had hbc hbd hprod
    · exact hdisj (meet_at_d hd_z)
    · have hprod : orient2 a b c * orient2 a b d < 0 :=
        mul_neg_of_neg_of_pos hc_n hd_p
      exact hdisj (segments_meet_of_opposite_sides hΔ_pos hab hac had hbc hbd hprod)
  · rcases lt_trichotomy (orient2 a b d) 0 with hd_n | hd_z | hd_p
    · exact hdisj (meet_at_c hc_z)
    · exact collinearSeparatedDiameterContradiction a b c d Δ h_ac h_ad h_bc h_bd
        hab hcd hac had hbc hbd ⟨hc_z, hd_z, hdisj⟩
    · exact hdisj (meet_at_c hc_z)
  · rcases lt_trichotomy (orient2 a b d) 0 with hd_n | hd_z | hd_p
    · have hprod : orient2 a b c * orient2 a b d < 0 :=
        mul_neg_of_pos_of_neg hc_p hd_n
      exact hdisj (segments_meet_of_opposite_sides hΔ_pos hab hac had hbc hbd hprod)
    · exact hdisj (meet_at_d hd_z)
    · have hprod : 0 < orient2 a b c * orient2 a b d := mul_pos hc_p hd_p
      exact sameSideDiameterContradiction a b c d Δ h_ac h_ad h_bc h_bd
        hab hcd hac had hbc hbd hprod

/-- Endpoint-disjoint diameter representative uniqueness, together with the
proved four-point diameter crossing theorem, gives simple meeting. -/
theorem endpoint_disjoint_diameter_representatives_meet_simply_from_unique_live
    (hUnique : EndpointDisjointDiameterIntersectionUniqueCertificate) :
    EndpointDisjointDiameterRepresentativesMeetSimply := by
  intro A Δ hΔ e he f hf hUne hNoShare
  classical
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  have hNoShareOrig : ¬ OrderedEdgesShareEndpoint (a, b) (c, d) := hNoShare
  rcases diameter_ordered_edges_cross_distances_le hΔ he hf with
    ⟨hab, hcd, hac, had, hbc, hbd⟩
  unfold OrderedEdgesShareEndpoint at hNoShare
  simp at hNoShare
  have h_ac : a ≠ c := hNoShare.1
  have h_ad : a ≠ d := hNoShare.2.1
  have h_bc : b ≠ c := hNoShare.2.2.1
  have h_bd : b ≠ d := hNoShare.2.2.2
  have hMeet : OrderedEdgesMeetGeometrically (a, b) (c, d) :=
    fourPointDiameterCrossing_thm a b c d Δ h_ac h_ad h_bc h_bd
      hab hcd hac had hbc hbd
  rcases hMeet with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact (hUnique A Δ hΔ (a, b) he (c, d) hf hUne hNoShareOrig x y hx hy).symm

/-- Live corrected Conway-form final assembly: support-level Conway counting,
endpoint-disjoint diameter intersection uniqueness, and pointwise deep-layer
screening imply Erdős #132.  The shared-endpoint diameter representative case is
already proved by `shared_endpoint_diameter_representatives_meet_simply`; the
endpoint-disjoint existence part is supplied by `fourPointDiameterCrossing_thm`.
-/
theorem erdos132_from_support_conway_endpoint_disjoint_uniqueness_and_deep_screening_live
    (hSupport : ConwayThrackleSupportBoundOnSupport)
    (hUnique : EndpointDisjointDiameterIntersectionUniqueCertificate)
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    Erdos132Ordered :=
  erdos132_from_diameter_sparsity_and_no_deep_layer
    (diameter_shell_sparse_from_diameter_conway_bound
      (diameter_conway_bound_from_support_conway hSupport
        (diameter_support_forms_conway_from_simple_representatives
          (diameter_support_simple_representatives_from_ordered_representatives
            (distinct_diameter_representatives_meet_simply_from_cases
              shared_endpoint_diameter_representatives_meet_simply
              (endpoint_disjoint_diameter_representatives_meet_simply_from_unique_live hUnique))))))
    (no_deep_layer_from_pointwise_screening_certificate hScreen)

/-- Live residual package after closing the shared-endpoint diameter
representative case. -/
structure Erdos132ConwayEndpointDisjointUniquenessScreeningResidualPack : Prop where
  support_conway_thrackle_bound : ConwayThrackleSupportBoundOnSupport
  endpoint_disjoint_diameter_intersection_unique :
    EndpointDisjointDiameterIntersectionUniqueCertificate
  pointwise_deep_layer_screening : PointwiseDeepLayerScreeningCertificate

/-- The live endpoint-disjoint uniqueness residual package proves Erdős #132. -/
theorem erdos132_from_conway_endpoint_disjoint_uniqueness_screening_residual_pack
    (P : Erdos132ConwayEndpointDisjointUniquenessScreeningResidualPack) :
    Erdos132Ordered :=
  erdos132_from_support_conway_endpoint_disjoint_uniqueness_and_deep_screening_live
    P.support_conway_thrackle_bound
    P.endpoint_disjoint_diameter_intersection_unique
    P.pointwise_deep_layer_screening

/-- Live final assembly with endpoint-disjoint uniqueness reduced to the
two-common-points-force-collinearity certificate. -/
theorem erdos132_from_support_conway_endpoint_disjoint_collinear_and_deep_screening_live
    (hSupport : ConwayThrackleSupportBoundOnSupport)
    (hCol : EndpointDisjointTwoPointIntersectionForcesCollinear)
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    Erdos132Ordered :=
  erdos132_from_support_conway_endpoint_disjoint_uniqueness_and_deep_screening_live
    hSupport
    (endpoint_disjoint_diameter_intersection_unique_from_two_point_collinear hCol)
    hScreen

/-- Live final assembly after closing all diameter-side local geometry.  The
remaining inputs are exactly support-level Conway counting and pointwise
deep-layer screening. -/
theorem erdos132_from_support_conway_and_deep_screening_live
    (hSupport : ConwayThrackleSupportBoundOnSupport)
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    Erdos132Ordered :=
  erdos132_from_support_conway_endpoint_disjoint_collinear_and_deep_screening_live
    hSupport
    endpoint_disjoint_two_point_intersection_forces_collinear
    hScreen

/-- Live final assembly with the remaining Conway input stated in the standard
ordered form.  The support-level wrapper is derived by choosing one ordered
representative from each unordered support edge. -/
theorem erdos132_from_ordered_conway_and_deep_screening_live
    (hConway : ConwayThrackleSupportBound)
    (hScreen : PointwiseDeepLayerScreeningCertificate) :
    Erdos132Ordered :=
  erdos132_from_support_conway_and_deep_screening_live
    (conway_support_bound_on_support_from_ordered hConway)
    hScreen

/-- Equivalent final assembly in the negative layer form: standard Conway
counting plus pointwise no-deep-layer contradiction proves Erdős #132. -/
theorem erdos132_from_ordered_conway_and_pointwise_no_deep_layer_live
    (hConway : ConwayThrackleSupportBound)
    (hNoDeep : PointwiseNoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_deep_screening_live
    hConway
    (pointwise_screening_certificate_from_no_deep_layer hNoDeep)

/-- Honest eventual final assembly.  The pointwise no-deep statement is too
strong for small finite sets; Erdős #132 only needs the eventual low-shell
no-deep theorem. -/
theorem erdos132_from_ordered_conway_and_eventual_no_deep_layer_live
    (hConway : ConwayThrackleSupportBound)
    (hNoDeep : NoDeepLayerCaseInLowShellRegime) :
    Erdos132Ordered :=
  erdos132_from_diameter_sparsity_and_no_deep_layer
    (diameter_shell_sparse_from_diameter_conway_bound
      (diameter_conway_bound_from_support_conway
        (conway_support_bound_on_support_from_ordered hConway)
        (diameter_support_forms_conway_from_simple_representatives
          (diameter_support_simple_representatives_from_ordered_representatives
            (distinct_diameter_representatives_meet_simply_from_cases
              shared_endpoint_diameter_representatives_meet_simply
              (endpoint_disjoint_diameter_representatives_meet_simply_from_unique_live
                (endpoint_disjoint_diameter_intersection_unique_from_two_point_collinear
                  endpoint_disjoint_two_point_intersection_forces_collinear)))))))
    hNoDeep

/-- Final assembly in the proof plan's current component language: standard
ordered Conway counting plus convex-layer screening proves Erdős #132. -/
theorem erdos132_from_ordered_conway_and_convex_layer_screening_live
    (hConway : ConwayThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_eventual_no_deep_layer_live
    hConway
    (no_deep_layer_from_convex_layer_screening hLayer)

/-- Final assembly with the layer residual stated as an explicit threshold. -/
theorem erdos132_from_ordered_conway_and_threshold_convex_layer_screening_live
    (hConway : ConwayThrackleSupportBound)
    (hLayer : ConvexLayerScreeningThresholdCertificate) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_convex_layer_screening_live
    hConway
    (convex_layer_screening_from_threshold hLayer)

/-- Current live residual package after reducing endpoint-disjoint uniqueness to
the two-point collinearity certificate. -/
structure Erdos132ConwayEndpointDisjointCollinearityScreeningResidualPack : Prop where
  support_conway_thrackle_bound : ConwayThrackleSupportBoundOnSupport
  endpoint_disjoint_two_point_intersection_forces_collinear :
    EndpointDisjointTwoPointIntersectionForcesCollinear
  pointwise_deep_layer_screening : PointwiseDeepLayerScreeningCertificate

/-- The endpoint-disjoint collinearity residual package proves Erdős #132. -/
theorem erdos132_from_conway_endpoint_disjoint_collinearity_screening_residual_pack
    (P : Erdos132ConwayEndpointDisjointCollinearityScreeningResidualPack) :
    Erdos132Ordered :=
  erdos132_from_support_conway_endpoint_disjoint_collinear_and_deep_screening_live
    P.support_conway_thrackle_bound
    P.endpoint_disjoint_two_point_intersection_forces_collinear
    P.pointwise_deep_layer_screening

/-- Current live residual package after closing the full diameter-side Conway
condition. -/
structure Erdos132ConwayCountingScreeningResidualPack : Prop where
  support_conway_thrackle_bound : ConwayThrackleSupportBoundOnSupport
  pointwise_deep_layer_screening : PointwiseDeepLayerScreeningCertificate

/-- The Conway-counting plus deep-screening residual package proves Erdős #132. -/
theorem erdos132_from_conway_counting_screening_residual_pack
    (P : Erdos132ConwayCountingScreeningResidualPack) :
    Erdos132Ordered :=
  erdos132_from_support_conway_and_deep_screening_live
    P.support_conway_thrackle_bound
    P.pointwise_deep_layer_screening

/-- Current live residual package in standard classical form: the standard
ordered Conway straight-line thrackle theorem plus pointwise deep-layer
screening. -/
structure Erdos132OrderedConwayScreeningResidualPack : Prop where
  ordered_conway_thrackle_bound : ConwayThrackleSupportBound
  pointwise_deep_layer_screening : PointwiseDeepLayerScreeningCertificate

/-- The standard Conway-counting plus deep-screening residual package proves
Erdős #132. -/
theorem erdos132_from_ordered_conway_screening_residual_pack
    (P : Erdos132OrderedConwayScreeningResidualPack) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_deep_screening_live
    P.ordered_conway_thrackle_bound
    P.pointwise_deep_layer_screening

/-- Final residual package in the cleanest negative layer form. -/
structure Erdos132OrderedConwayNoDeepResidualPack : Prop where
  ordered_conway_thrackle_bound : ConwayThrackleSupportBound
  pointwise_no_deep_layer : PointwiseNoDeepLayerCaseInLowShellRegime

/-- The ordered Conway plus pointwise no-deep residual package proves Erdős #132. -/
theorem erdos132_from_ordered_conway_no_deep_residual_pack
    (P : Erdos132OrderedConwayNoDeepResidualPack) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_pointwise_no_deep_layer_live
    P.ordered_conway_thrackle_bound
    P.pointwise_no_deep_layer

/-- Honest final residual package: standard ordered Conway counting plus the
eventual low-shell no-deep theorem. -/
structure Erdos132OrderedConwayEventualNoDeepResidualPack : Prop where
  ordered_conway_thrackle_bound : ConwayThrackleSupportBound
  eventual_no_deep_layer : NoDeepLayerCaseInLowShellRegime

/-- The honest eventual residual package proves Erdős #132. -/
theorem erdos132_from_ordered_conway_eventual_no_deep_residual_pack
    (P : Erdos132OrderedConwayEventualNoDeepResidualPack) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_eventual_no_deep_layer_live
    P.ordered_conway_thrackle_bound
    P.eventual_no_deep_layer

/-- Final residual package in the proof plan's component language: standard
ordered Conway counting plus convex-layer screening. -/
structure Erdos132OrderedConwayConvexLayerResidualPack : Prop where
  ordered_conway_thrackle_bound : ConwayThrackleSupportBound
  convex_layer_screening : ConvexLayerScreeningBridge

/-- Ordered Conway counting plus convex-layer screening proves Erdős #132. -/
theorem erdos132_from_ordered_conway_convex_layer_residual_pack
    (P : Erdos132OrderedConwayConvexLayerResidualPack) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_convex_layer_screening_live
    P.ordered_conway_thrackle_bound
    P.convex_layer_screening

/-- Final residual package with an explicit convex-layer threshold. -/
structure Erdos132OrderedConwayThresholdLayerResidualPack : Prop where
  ordered_conway_thrackle_bound : ConwayThrackleSupportBound
  convex_layer_screening_threshold : ConvexLayerScreeningThresholdCertificate

/-- Ordered Conway counting plus thresholded convex-layer screening proves
Erdős #132. -/
theorem erdos132_from_ordered_conway_threshold_layer_residual_pack
    (P : Erdos132OrderedConwayThresholdLayerResidualPack) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_threshold_convex_layer_screening_live
    P.ordered_conway_thrackle_bound
    P.convex_layer_screening_threshold

/-- The current live two-input endpoint for Erdős #132.  All finite accounting,
diameter geometry, ordered/unordered representative bookkeeping, and the
support-level Conway correction have been discharged above. -/
def Erdos132CurrentLiveResidual : Prop :=
  ConwayThrackleSupportBound ∧ ConvexLayerScreeningBridge

/-- The current live two-input residual proves Erdős #132. -/
theorem erdos132_from_current_live_residual
    (h : Erdos132CurrentLiveResidual) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_convex_layer_screening_live h.1 h.2

/-- Constructive version of the current live residual: a Conway endpoint-charge
certificate plus convex-layer screening proves Erdős #132. -/
def Erdos132CurrentConstructiveResidual : Prop :=
  ConwayThrackleEndpointChargeCertificate ∧ ConvexLayerScreeningBridge

/-- The constructive current residual proves Erdős #132. -/
theorem erdos132_from_current_constructive_residual
    (h : Erdos132CurrentConstructiveResidual) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_convex_layer_screening_live
    (conway_support_bound_from_endpoint_charge h.1)
    h.2

/-- Large non-star version of the current live residual: all small and star
Conway cases are closed by finite bookkeeping, so only the large non-star
Conway theorem remains on the counting side. -/
def Erdos132CurrentLargeNonStarResidual : Prop :=
  LargeNonStarConwayThrackleSupportBound ∧ ConvexLayerScreeningBridge

/-- The large non-star current residual proves Erdős #132. -/
theorem erdos132_from_current_large_nonstar_residual
    (h : Erdos132CurrentLargeNonStarResidual) :
    Erdos132Ordered :=
  erdos132_from_ordered_conway_and_convex_layer_screening_live
    (conway_support_bound_from_large_nonstar h.1)
    h.2

/-- Legacy reduced assembly retained for comparison with the pre-Conway-correction
proof graph.  The live final endpoint is
`erdos132_from_ordered_conway_convex_layer_residual_pack`. -/
theorem erdos132_from_thrackle_and_layer
    (hSupport : UndirectedThrackleSupportBound)
    (hLayer : ConvexLayerScreeningBridge) :
    Erdos132Ordered :=
  erdos132_from_four_point_thrackle_and_convex_layer_screening
    fourPointDiameterCrossing_thm hSupport hLayer

end
end DistanceShellMultiplicity
end Mathematics
end IndisputableMonolith
