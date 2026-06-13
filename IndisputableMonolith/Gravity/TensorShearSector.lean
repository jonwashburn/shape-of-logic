import Mathlib
import IndisputableMonolith.Geometry.ReggeActionFirstVariation
import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus

/-!
# Track 1.D tensor/shear sector scaffold

The existing Track 1.B conformal ansatz assigns one scalar potential to each
vertex and induces edge-length variations by averaging endpoint potentials.
That scalar slice is not the full weak-field metric sector: it cannot represent
pure shear, hence cannot by itself cover transverse-traceless gravitational-wave
modes.

This file starts the tensor/shear track by separating independent edge
perturbations from vertex-conformal perturbations and by proving the elementary
rectangle obstruction for the conformal ansatz.
-/

namespace IndisputableMonolith
namespace Gravity
namespace TensorShearSector

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.ReggeActionFirstVariation
open Geometry.Triangulation3DConsistency
open Geometry.PeriodicFreudenthalTorus

noncomputable section

/-- Edge-level length perturbations.  Unlike `VertexPotential`, this has one
degree of freedom per global edge and is the natural finite Regge surface for
anisotropic shear and TT modes. -/
abbrev EdgePerturbation (K : Triangulation3D) :=
  Fin K.nE → ℝ

/-- The first-order log-length strain induced by the vertex-conformal ansatz. -/
def conformalEdgeLogStrain (K : Triangulation3D) (ξ : VertexPotential K) :
    EdgePerturbation K :=
  fun e =>
    let uv := K.edgeVerts e
    (ξ uv.1 + ξ uv.2) / 2

/-- The actual first-order length variation induced by the conformal ansatz. -/
def conformalEdgeLengthPerturbation
    (K : Triangulation3D) (hK : IncidenceConsistent K) (ξ : VertexPotential K) :
    EdgePerturbation K :=
  fun e => hingeMeasureDirectionalDeriv K hK ξ e

theorem conformalEdgeLengthPerturbation_eq_sqrt_mul_logStrain
    (K : Triangulation3D) (hK : IncidenceConsistent K) (ξ : VertexPotential K)
    (e : Fin K.nE) :
    conformalEdgeLengthPerturbation K hK ξ e =
      Real.sqrt (hK.globalSqEdge e) * conformalEdgeLogStrain K ξ e := by
  rfl

/-- The subspace of edge perturbations that come from vertex-conformal
potentials.  Track 1.B lives inside this subspace. -/
def IsConformalEdgePerturbation (K : Triangulation3D) (ε : EdgePerturbation K) : Prop :=
  ∃ ξ : VertexPotential K, ε = conformalEdgeLogStrain K ξ

/-- Rectangle obstruction in first-order log strains.  If a quadrilateral's two
opposite horizontal edges have conformal log-strain `h` and its two opposite
vertical edges have conformal log-strain `v`, then `h = v`.  Hence a nontrivial
rectangle/shear mode cannot be vertex-conformal. -/
theorem vertexConformal_rectangle_log_strain_forces_square
    (ξa ξb ξc ξd h v : ℝ)
    (hab : (ξa + ξb) / 2 = h)
    (hcd : (ξc + ξd) / 2 = h)
    (hbc : (ξb + ξc) / 2 = v)
    (hda : (ξd + ξa) / 2 = v) :
    h = v := by
  linarith

/-- A nontrivial rectangle/shear strain (`h ≠ v`) has no vertex-conformal
potential realization. -/
theorem nontrivial_rectangle_shear_not_vertexConformal
    (h v : ℝ) (hne : h ≠ v) :
    ¬ ∃ ξa ξb ξc ξd : ℝ,
      (ξa + ξb) / 2 = h ∧
      (ξc + ξd) / 2 = h ∧
      (ξb + ξc) / 2 = v ∧
      (ξd + ξa) / 2 = v := by
  rintro ⟨ξa, ξb, ξc, ξd, hab, hcd, hbc, hda⟩
  exact hne (vertexConformal_rectangle_log_strain_forces_square
    ξa ξb ξc ξd h v hab hcd hbc hda)

/-! ## Concrete `N = 5` periodic Freudenthal edge surface -/

abbrev PeriodicVertex5 :=
  Vertex 5 5 5

abbrev PeriodicEdge5 :=
  PeriodicEdge 5 5 5

/-- The canonical encoded `5 × 5 × 5` periodic Freudenthal torus for Track 1.D. -/
noncomputable abbrev PeriodicTorus5 :=
  canonicalEncodedPeriodicFreudenthalTorus 5 5 5 (by decide) (by decide) (by decide)

/-- External vertex decoder matching the numerical order used by the Track 1.D
payload generators: `vertex_index = (x * 5 + y) * 5 + z`. -/
def periodicExternalVertexOfIndex5 (idx : Nat) : PeriodicVertex5 :=
  (⟨(idx / 25) % 5, by omega⟩,
   ⟨(idx / 5) % 5, by omega⟩,
   ⟨idx % 5, by omega⟩)

/-- External vertex encoder matching `periodicExternalVertexOfIndex5` on
in-range payload vertices. -/
def periodicExternalVertexIndex5 (v : PeriodicVertex5) : Nat :=
  (v.1.1 * 5 + v.2.1.1) * 5 + v.2.2.1

/-- External edge decoder matching the numerical order used by the Track 1.D
payload generators: `edge_index = vertex_index * 7 + disp`.  This is a
computable, Lean-native companion to the canonical `PeriodicTorus5.edgeEquiv`,
whose current implementation goes through opaque `Fintype.equivFin` order. -/
def periodicExternalEdgeOfEncodedIdx5
    (idx : Fin PeriodicTorus5.K.nE) : PeriodicEdge5 :=
  { base := periodicExternalVertexOfIndex5 (idx.1 / 7)
    disp := ⟨idx.1 % 7, by omega⟩ }

/-- External edge encoder matching the numerical order used by the Track 1.D
payload generators. -/
def periodicExternalEdgeIndex5 (e : PeriodicEdge5) : Nat :=
  periodicExternalVertexIndex5 e.base * 7 + e.disp.1

/-- Canonical encoded vertex index equivalence for the concrete `N = 5` torus. -/
noncomputable abbrev periodicVertexEquiv5 :
    Fin PeriodicTorus5.K.nV ≃ PeriodicVertex5 :=
  vertexFinEquiv 5 5 5

/-- Coordinate addition on the concrete `N = 5` torus. -/
def periodicAddFin5 (base v : Fin 5) : Fin 5 :=
  ⟨(base.1 + v.1) % 5, by omega⟩

/-- Translate a vertex by another vertex on the concrete `N = 5` torus. -/
def periodicTranslateVertex5 (base v : PeriodicVertex5) : PeriodicVertex5 :=
  (periodicAddFin5 base.1 v.1,
   periodicAddFin5 base.2.1 v.2.1,
   periodicAddFin5 base.2.2 v.2.2)

/-- Encoded vertex-index shift corresponding to translation by a typed row base. -/
noncomputable def periodicTranslateEncodedVertexIdx5
    (base : PeriodicVertex5) (v : Fin PeriodicTorus5.K.nV) :
    Fin PeriodicTorus5.K.nV :=
  periodicVertexEquiv5.symm (periodicTranslateVertex5 base (periodicVertexEquiv5 v))

/-- The encoded torus endpoint map agrees with the typed periodic-edge
endpoints after transporting through the canonical vertex equivalence. -/
theorem periodicTorus5_edgeVerts_symm_eq_endpoints
    (e : PeriodicEdge5) :
    PeriodicTorus5.K.edgeVerts (PeriodicTorus5.edgeEquiv.symm e) =
      (periodicVertexEquiv5.symm e.endpoints.1,
       periodicVertexEquiv5.symm e.endpoints.2) := by
  simp [periodicVertexEquiv5,
    canonicalEncodedPeriodicFreudenthalTorus,
    canonicalEncodedPeriodicFreudenthalTorus_of_endpoint,
    canonicalEncodedPeriodicFreudenthalTorus_of_incidence,
    canonicalPeriodicTriangulation, canonicalPeriodicEdgeEquiv,
    canonicalEdgeVerts]

/-- Edge perturbations indexed by the typed periodic Freudenthal edges. -/
abbrev PeriodicEdgePerturbation5 :=
  PeriodicEdge5 → ℝ

/-- Edge perturbations indexed by the encoded finite triangulation edges. -/
abbrev EncodedEdgePerturbation5 :=
  EdgePerturbation PeriodicTorus5.K

/-- Pull an encoded finite edge perturbation back to typed periodic edges. -/
def encodedToPeriodicEdgePerturbation5
    (ε : EncodedEdgePerturbation5) : PeriodicEdgePerturbation5 :=
  fun e => ε (PeriodicTorus5.edgeEquiv.symm e)

/-- Push a typed periodic edge perturbation to encoded finite edge indices. -/
def periodicToEncodedEdgePerturbation5
    (ε : PeriodicEdgePerturbation5) : EncodedEdgePerturbation5 :=
  fun e => ε (PeriodicTorus5.edgeEquiv e)

/-- The encoded `Fin K.nE` and typed periodic-edge views of the `N = 5`
tensor/shear perturbation surface are exactly equivalent. -/
noncomputable def periodicEdgePerturbationEquiv5 :
    EncodedEdgePerturbation5 ≃ PeriodicEdgePerturbation5 where
  toFun := encodedToPeriodicEdgePerturbation5
  invFun := periodicToEncodedEdgePerturbation5
  left_inv := by
    intro ε
    funext e
    simp [encodedToPeriodicEdgePerturbation5, periodicToEncodedEdgePerturbation5]
  right_inv := by
    intro ε
    funext e
    simp [encodedToPeriodicEdgePerturbation5, periodicToEncodedEdgePerturbation5]

/-- Raw additive splitting datum for an edge-perturbation space.  This carries
only the algebraic reconstruction identity; the real Track 1.D target below
adds conformal, gauge, and TT membership predicates. -/
structure RawEdgePerturbationSplitting (E : Type) where
  conformalPart : (E → ℝ) → E → ℝ
  gaugePart : (E → ℝ) → E → ℝ
  ttPart : (E → ℝ) → E → ℝ
  reconstruct :
    ∀ ε : E → ℝ, ∀ e : E,
      conformalPart ε e + gaugePart ε e + ttPart ε e = ε e

/-- The concrete next target for Track 1.D after Session 215.  The three
predicates must be supplied by the actual periodic Freudenthal operators:
conformal/trace, gauge/longitudinal, and TT/transverse-traceless. -/
def PeriodicFreudenthalTTDecompositionTargetAtN5
    (IsConformal IsGauge IsTT : PeriodicEdgePerturbation5 → Prop) : Prop :=
  ∃ split : RawEdgePerturbationSplitting PeriodicEdge5,
    (∀ ε, IsConformal (split.conformalPart ε)) ∧
    (∀ ε, IsGauge (split.gaugePart ε)) ∧
    (∀ ε, IsTT (split.ttPart ε))

/-- Carry any decomposition on encoded finite edges across the canonical
periodic-edge equivalence. -/
noncomputable def periodicRawSplittingOfEncoded5
    (D : RawEdgePerturbationSplitting (Fin PeriodicTorus5.K.nE)) :
    RawEdgePerturbationSplitting PeriodicEdge5 where
  conformalPart ε :=
    encodedToPeriodicEdgePerturbation5
      (D.conformalPart (periodicToEncodedEdgePerturbation5 ε))
  gaugePart ε :=
    encodedToPeriodicEdgePerturbation5
      (D.gaugePart (periodicToEncodedEdgePerturbation5 ε))
  ttPart ε :=
    encodedToPeriodicEdgePerturbation5
      (D.ttPart (periodicToEncodedEdgePerturbation5 ε))
  reconstruct := by
    intro ε e
    simp [encodedToPeriodicEdgePerturbation5, periodicToEncodedEdgePerturbation5,
      D.reconstruct]

/-! ## Orthogonal conformal/gauge/TT surface -/

/-- The finite `N = 5` edge-space inner product used for the tensor/shear
decomposition. -/
def periodicEdgeInnerProduct5
    (ε η : PeriodicEdgePerturbation5) : ℝ :=
  ∑ e : PeriodicEdge5, ε e * η e

theorem periodicEdgeInnerProduct5_symm
    (ε η : PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 ε η = periodicEdgeInnerProduct5 η ε := by
  unfold periodicEdgeInnerProduct5
  refine Finset.sum_congr rfl ?_
  intro e _
  ring

theorem periodicEdgeInnerProduct5_zero_left
    (η : PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 (fun _ => 0) η = 0 := by
  simp [periodicEdgeInnerProduct5]

theorem periodicEdgeInnerProduct5_zero_right
    (ε : PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 ε (fun _ => 0) = 0 := by
  simp [periodicEdgeInnerProduct5]

theorem periodicEdgeInnerProduct5_add_right
    (ε η ζ : PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 ε (fun e => η e + ζ e) =
      periodicEdgeInnerProduct5 ε η + periodicEdgeInnerProduct5 ε ζ := by
  unfold periodicEdgeInnerProduct5
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _
  ring

set_option maxRecDepth 65536

/-- On the finite real periodic-edge space, zero self-inner-product forces the
edge perturbation itself to vanish. -/
theorem periodicEdgePerturbation5_eq_zero_of_inner_self_eq_zero
    (ε : PeriodicEdgePerturbation5)
    (h : periodicEdgeInnerProduct5 ε ε = 0) :
    ε = fun _ => 0 := by
  funext e
  have hsum : (∑ x : PeriodicEdge5, ε x * ε x) = 0 := by
    simpa [periodicEdgeInnerProduct5] using h
  by_contra hne
  have hpos : 0 < ε e * ε e := mul_self_pos.mpr hne
  have hsum_pos : 0 < ∑ x : PeriodicEdge5, ε x * ε x := by
    exact Finset.sum_pos'
      (fun x _ => mul_self_nonneg (ε x))
      ⟨e, Finset.mem_univ e, hpos⟩
  rw [hsum] at hsum_pos
  exact (lt_irrefl (0 : ℝ) hsum_pos).elim

/-- The periodic-edge version of the vertex-conformal/log-strain subspace. -/
def PeriodicConformalLogSubspace5
    (ε : PeriodicEdgePerturbation5) : Prop :=
  ∃ ξ : VertexPotential PeriodicTorus5.K,
    ε = encodedToPeriodicEdgePerturbation5 (conformalEdgeLogStrain PeriodicTorus5.K ξ)

theorem periodicConformalLogSubspace5_zero :
    PeriodicConformalLogSubspace5 (fun _ => 0) := by
  refine ⟨fun _ => 0, ?_⟩
  funext e
  simp [encodedToPeriodicEdgePerturbation5, conformalEdgeLogStrain]

/-- Encoded vertex delta used to generate the finite conformal subspace. -/
def encodedVertexDeltaPotential5
    (v : Fin PeriodicTorus5.K.nV) : VertexPotential PeriodicTorus5.K :=
  fun w => if w = v then 1 else 0

/-- The conformal generator obtained by putting unit potential at one encoded
vertex and zero potential at the others. -/
def periodicConformalGenerator5
    (v : Fin PeriodicTorus5.K.nV) : PeriodicEdgePerturbation5 :=
  encodedToPeriodicEdgePerturbation5
    (conformalEdgeLogStrain PeriodicTorus5.K (encodedVertexDeltaPotential5 v))

/-- Pointwise form of the conformal vertex-delta edge generator in typed
periodic-edge coordinates. -/
theorem periodicConformalGenerator5_apply_endpoint
    (v : Fin PeriodicTorus5.K.nV) (e : PeriodicEdge5) :
    periodicConformalGenerator5 v e =
      ((if periodicVertexEquiv5.symm e.endpoints.1 = v then 1 else 0) +
        (if periodicVertexEquiv5.symm e.endpoints.2 = v then 1 else 0)) / 2 := by
  unfold periodicConformalGenerator5 encodedToPeriodicEdgePerturbation5
    conformalEdgeLogStrain encodedVertexDeltaPotential5
  rw [periodicTorus5_edgeVerts_symm_eq_endpoints]

/-- The concrete `N = 5` conformal slice is spanned by encoded vertex delta
generators.  This supplies the conformal half of the finite-generator TT
projector data. -/
theorem periodicConformalLogSubspace5_spanned_by_encodedVertexGenerators
    (c : PeriodicEdgePerturbation5)
    (hc : PeriodicConformalLogSubspace5 c) :
    ∃ coeff : Fin PeriodicTorus5.K.nV → ℝ,
      ∀ e, c e = ∑ v : Fin PeriodicTorus5.K.nV,
        coeff v * periodicConformalGenerator5 v e := by
  classical
  rcases hc with ⟨ξ, rfl⟩
  refine ⟨ξ, ?_⟩
  intro e
  unfold periodicConformalGenerator5 encodedVertexDeltaPotential5
    encodedToPeriodicEdgePerturbation5 conformalEdgeLogStrain
  simp [Finset.mul_sum, Finset.sum_add_distrib, div_eq_mul_inv, mul_add,
    mul_assoc, mul_comm]

/-- A gauge subspace supplied by a concrete forward Track 1.D gauge operator. The
operator remains a parameter here, so this file does not pretend to have already
chosen the longitudinal/diffeomorphism discretization. -/
def PeriodicGaugeSubspace5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5)
    (ε : PeriodicEdgePerturbation5) : Prop :=
  ∃ A : GaugePotential, ε = gaugeMap A

/-- TT means orthogonal to the conformal slice and to the supplied gauge slice
with respect to the finite periodic-edge inner product. -/
def PeriodicTTOrthogonal5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5)
    (ε : PeriodicEdgePerturbation5) : Prop :=
  (∀ c : PeriodicEdgePerturbation5,
      PeriodicConformalLogSubspace5 c → periodicEdgeInnerProduct5 ε c = 0) ∧
  (∀ g : PeriodicEdgePerturbation5,
      PeriodicGaugeSubspace5 GaugePotential gaugeMap g →
        periodicEdgeInnerProduct5 ε g = 0)

theorem periodicTTOrthogonal5_zero
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5) :
    PeriodicTTOrthogonal5 GaugePotential gaugeMap (fun _ => 0) := by
  constructor
  · intro c _
    exact periodicEdgeInnerProduct5_zero_left c
  · intro g _
    exact periodicEdgeInnerProduct5_zero_left g

/-- Honest Track 1.D decomposition target with TT interpreted as finite
orthogonality to the conformal and gauge subspaces.  The remaining mathematical
load is the construction of the three projectors. -/
def PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5) : Prop :=
  ∃ split : RawEdgePerturbationSplitting PeriodicEdge5,
    (∀ ε, PeriodicConformalLogSubspace5 (split.conformalPart ε)) ∧
    (∀ ε, PeriodicGaugeSubspace5 GaugePotential gaugeMap (split.gaugePart ε)) ∧
    (∀ ε, PeriodicTTOrthogonal5 GaugePotential gaugeMap (split.ttPart ε))

/-- Concrete projector data needed to close the finite `N = 5` conformal/gauge/TT
decomposition.  This is still a theorem-shaped target: the tensor lane must
construct these three maps for the chosen gauge operator and prove membership
plus pointwise reconstruction. -/
structure PeriodicTTProjectorData5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5) where
  conformalProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  conformal_mem :
    ∀ ε, PeriodicConformalLogSubspace5 (conformalProjector ε)
  gauge_mem :
    ∀ ε, PeriodicGaugeSubspace5 GaugePotential gaugeMap (gaugeProjector ε)
  tt_mem :
    ∀ ε, PeriodicTTOrthogonal5 GaugePotential gaugeMap (ttProjector ε)
  reconstruct :
    ∀ ε e, conformalProjector ε e + gaugeProjector ε e + ttProjector ε e = ε e

/-- Linearity of the finite periodic-edge inner product in the right argument,
specialized to a finite linear combination. -/
theorem periodicEdgeInnerProduct5_linear_combo_right
    {ι : Type} [Fintype ι]
    (ε : PeriodicEdgePerturbation5)
    (coeff : ι → ℝ) (basis : ι → PeriodicEdgePerturbation5) :
    periodicEdgeInnerProduct5 ε (fun e => ∑ i : ι, coeff i * basis i e) =
      ∑ i : ι, coeff i * periodicEdgeInnerProduct5 ε (basis i) := by
  classical
  unfold periodicEdgeInnerProduct5
  calc
    (∑ e : PeriodicEdge5, ε e * (∑ i : ι, coeff i * basis i e)) =
        ∑ e : PeriodicEdge5, ∑ i : ι, ε e * (coeff i * basis i e) := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [Finset.mul_sum]
    _ = ∑ i : ι, ∑ e : PeriodicEdge5, ε e * (coeff i * basis i e) := by
          rw [Finset.sum_comm]
    _ = ∑ i : ι, coeff i * ∑ e : PeriodicEdge5, ε e * basis i e := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro e _
          ring

/-- Finite-generator projector data.  This is the next concrete Track 1.D proof
surface: give finite spanning families for the conformal and gauge slices, then
construct projectors whose TT residual is orthogonal to every generator. -/
structure PeriodicTTFiniteGeneratorProjectorData5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5)
    (CIdx GIdx : Type) [Fintype CIdx] [Fintype GIdx] where
  conformalProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  conformalGen : CIdx → PeriodicEdgePerturbation5
  gaugeGen : GIdx → PeriodicEdgePerturbation5
  conformal_mem :
    ∀ ε, PeriodicConformalLogSubspace5 (conformalProjector ε)
  gauge_mem :
    ∀ ε, PeriodicGaugeSubspace5 GaugePotential gaugeMap (gaugeProjector ε)
  conformal_span :
    ∀ c, PeriodicConformalLogSubspace5 c →
      ∃ coeff : CIdx → ℝ, ∀ e, c e = ∑ i : CIdx, coeff i * conformalGen i e
  gauge_span :
    ∀ g, PeriodicGaugeSubspace5 GaugePotential gaugeMap g →
      ∃ coeff : GIdx → ℝ, ∀ e, g e = ∑ i : GIdx, coeff i * gaugeGen i e
  tt_orthogonal_conformal_gen :
    ∀ ε i, periodicEdgeInnerProduct5 (ttProjector ε) (conformalGen i) = 0
  tt_orthogonal_gauge_gen :
    ∀ ε i, periodicEdgeInnerProduct5 (ttProjector ε) (gaugeGen i) = 0
  reconstruct :
    ∀ ε e, conformalProjector ε e + gaugeProjector ε e + ttProjector ε e = ε e

/-- The gauge map generated by a finite family of longitudinal edge
perturbations.  Gauge potentials are coefficient vectors on the supplied
generators. -/
def periodicGaugeGeneratorMap5
    {GIdx : Type} [Fintype GIdx]
    (gaugeGen : GIdx → PeriodicEdgePerturbation5) :
    (GIdx → ℝ) → PeriodicEdgePerturbation5 :=
  fun coeff e => ∑ i : GIdx, coeff i * gaugeGen i e

/-- The conformal projector generated by coefficients on the encoded vertex
delta basis. -/
def periodicConformalGeneratorMap5 :
    (Fin PeriodicTorus5.K.nV → ℝ) → PeriodicEdgePerturbation5 :=
  periodicGaugeGeneratorMap5 periodicConformalGenerator5

/-- The conformal generator map has two-point support on a concrete edge: only
the base and head endpoint coefficients contribute. -/
theorem periodicConformalGeneratorMap5_apply_endpoint
    (coeff : Fin PeriodicTorus5.K.nV → ℝ) (e : PeriodicEdge5) :
    periodicConformalGeneratorMap5 coeff e =
      (coeff (periodicVertexEquiv5.symm e.endpoints.1) +
        coeff (periodicVertexEquiv5.symm e.endpoints.2)) / 2 := by
  classical
  unfold periodicConformalGeneratorMap5 periodicGaugeGeneratorMap5
  simp [periodicConformalGenerator5_apply_endpoint, Finset.sum_add_distrib,
    div_eq_mul_inv, mul_add, mul_comm]

/-- Any coefficient vector on the encoded vertex-delta conformal generators
lands in the conformal subspace. -/
theorem periodicConformalGeneratorMap5_mem
    (coeff : Fin PeriodicTorus5.K.nV → ℝ) :
    PeriodicConformalLogSubspace5 (periodicConformalGeneratorMap5 coeff) := by
  classical
  refine ⟨coeff, ?_⟩
  funext e
  unfold periodicConformalGeneratorMap5 periodicGaugeGeneratorMap5
    periodicConformalGenerator5 encodedVertexDeltaPotential5
    encodedToPeriodicEdgePerturbation5 conformalEdgeLogStrain
  simp [Finset.mul_sum, Finset.sum_add_distrib, div_eq_mul_inv, mul_add,
    mul_assoc, mul_comm]

/-- The image of a generator-defined gauge map is spanned by its generators by
construction. -/
theorem periodicGaugeSubspace5_spanned_by_generatorMap
    {GIdx : Type} [Fintype GIdx]
    (gaugeGen : GIdx → PeriodicEdgePerturbation5)
    (g : PeriodicEdgePerturbation5)
    (hg : PeriodicGaugeSubspace5 (GIdx → ℝ) (periodicGaugeGeneratorMap5 gaugeGen) g) :
    ∃ coeff : GIdx → ℝ, ∀ e, g e = ∑ i : GIdx, coeff i * gaugeGen i e := by
  rcases hg with ⟨coeff, rfl⟩
  exact ⟨coeff, fun _ => rfl⟩

/-- Index type for the concrete periodic longitudinal gauge basis: one vector
component at one periodic vertex. -/
abbrev PeriodicLongitudinalGaugeIdx5 :=
  PeriodicVertex5 × Fin 3

/-- Translate a concrete longitudinal gauge basis index by a typed row base. -/
def periodicTranslateLongitudinalGaugeIdx5
    (base : PeriodicVertex5) (idx : PeriodicLongitudinalGaugeIdx5) :
    PeriodicLongitudinalGaugeIdx5 :=
  (periodicTranslateVertex5 base idx.1, idx.2)

/-- Coordinate component of one of the seven positive Freudenthal edge
displacements. -/
def periodicDispCoord5 (disp : Fin 7) (j : Fin 3) : ℝ :=
  let bits := dispBits disp
  match j with
  | ⟨0, _⟩ => if bits.1 then 1 else 0
  | ⟨1, _⟩ => if bits.2.1 then 1 else 0
  | ⟨2, _⟩ => if bits.2.2 then 1 else 0

/-- Concrete finite longitudinal gauge generator on periodic edge strains.  It is
the signed edge-direction component of a unit vector field at one vertex:
positive at the head endpoint and negative at the base endpoint. -/
def periodicLongitudinalGaugeGenerator5
    (idx : PeriodicLongitudinalGaugeIdx5) : PeriodicEdgePerturbation5 :=
  fun e =>
    let d := periodicDispCoord5 e.disp idx.2
    (if e.endpoints.2 = idx.1 then d else 0) -
      (if e.endpoints.1 = idx.1 then d else 0)

/-- The concrete finite longitudinal gauge map generated by vertex-vector delta
basis elements. -/
def periodicLongitudinalGaugeMap5 :
    (PeriodicLongitudinalGaugeIdx5 → ℝ) → PeriodicEdgePerturbation5 :=
  periodicGaugeGeneratorMap5 periodicLongitudinalGaugeGenerator5

/-- The longitudinal gauge map has endpoint support on a concrete edge: only
the three component coefficients at the edge base and head contribute. -/
theorem periodicLongitudinalGaugeMap5_apply_endpoint
    (coeff : PeriodicLongitudinalGaugeIdx5 → ℝ) (e : PeriodicEdge5) :
    periodicLongitudinalGaugeMap5 coeff e =
      ∑ c : Fin 3,
        (coeff (e.endpoints.2, c) - coeff (e.endpoints.1, c)) *
          periodicDispCoord5 e.disp c := by
  classical
  unfold periodicLongitudinalGaugeMap5 periodicGaugeGeneratorMap5
    periodicLongitudinalGaugeGenerator5
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_sub_distrib, mul_sub, mul_comm]

/-- The concrete longitudinal gauge map is, by definition, generated by the
vertex-vector longitudinal basis. -/
theorem periodicLongitudinalGaugeMap5_eq_generatorMap :
    periodicLongitudinalGaugeMap5 =
      periodicGaugeGeneratorMap5 periodicLongitudinalGaugeGenerator5 :=
  rfl

/-- Concrete TT predicate for the fixed longitudinal-gauge tensor sector. -/
abbrev PeriodicLongitudinalTTSubspace5 :=
  PeriodicTTOrthogonal5
    (PeriodicLongitudinalGaugeIdx5 → ℝ)
    periodicLongitudinalGaugeMap5

/-- The concrete longitudinal gauge image is spanned by the vertex-vector delta
generators. -/
theorem periodicGaugeSubspace5_spanned_by_longitudinalGeneratorMap
    (g : PeriodicEdgePerturbation5)
    (hg : PeriodicGaugeSubspace5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 g) :
    ∃ coeff : PeriodicLongitudinalGaugeIdx5 → ℝ,
      ∀ e, g e =
        ∑ i : PeriodicLongitudinalGaugeIdx5,
          coeff i * periodicLongitudinalGaugeGenerator5 i e := by
  exact periodicGaugeSubspace5_spanned_by_generatorMap
    periodicLongitudinalGaugeGenerator5 g hg

/-- Gauge-generator projector data, with the conformal generators fixed to the
encoded vertex-delta family already proved to span the conformal slice.  This is
the sharper Track 1.D target after the conformal half has been discharged. -/
structure PeriodicTTGaugeGeneratorProjectorData5
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5)
    (GIdx : Type) [Fintype GIdx] where
  conformalProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeGen : GIdx → PeriodicEdgePerturbation5
  conformal_mem :
    ∀ ε, PeriodicConformalLogSubspace5 (conformalProjector ε)
  gauge_mem :
    ∀ ε, PeriodicGaugeSubspace5 GaugePotential gaugeMap (gaugeProjector ε)
  gauge_span :
    ∀ g, PeriodicGaugeSubspace5 GaugePotential gaugeMap g →
      ∃ coeff : GIdx → ℝ, ∀ e, g e = ∑ i : GIdx, coeff i * gaugeGen i e
  tt_orthogonal_conformal_gen :
    ∀ ε v, periodicEdgeInnerProduct5 (ttProjector ε) (periodicConformalGenerator5 v) = 0
  tt_orthogonal_gauge_gen :
    ∀ ε i, periodicEdgeInnerProduct5 (ttProjector ε) (gaugeGen i) = 0
  reconstruct :
    ∀ ε e, conformalProjector ε e + gaugeProjector ε e + ttProjector ε e = ε e

/-- Projector data for a gauge map that is itself defined by finite generators.
This removes a separate gauge-span obligation: the gauge map is the span. -/
structure PeriodicTTGeneratorMapProjectorData5
    (GIdx : Type) [Fintype GIdx] where
  conformalProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeCoeffProjector : PeriodicEdgePerturbation5 → GIdx → ℝ
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeGen : GIdx → PeriodicEdgePerturbation5
  conformal_mem :
    ∀ ε, PeriodicConformalLogSubspace5 (conformalProjector ε)
  tt_orthogonal_conformal_gen :
    ∀ ε v, periodicEdgeInnerProduct5 (ttProjector ε) (periodicConformalGenerator5 v) = 0
  tt_orthogonal_gauge_gen :
    ∀ ε i, periodicEdgeInnerProduct5 (ttProjector ε) (gaugeGen i) = 0
  reconstruct :
    ∀ ε e,
      conformalProjector ε e +
        periodicGaugeGeneratorMap5 gaugeGen (gaugeCoeffProjector ε) e +
        ttProjector ε e = ε e

/-- Projector data for the concrete periodic longitudinal gauge basis.  This is
now the exact finite-dimensional decomposition input still owed by Track 1.D. -/
structure PeriodicTTLongitudinalProjectorData5 where
  conformalProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  gaugeCoeffProjector :
    PeriodicEdgePerturbation5 → PeriodicLongitudinalGaugeIdx5 → ℝ
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  conformal_mem :
    ∀ ε, PeriodicConformalLogSubspace5 (conformalProjector ε)
  tt_orthogonal_conformal_gen :
    ∀ ε v, periodicEdgeInnerProduct5 (ttProjector ε) (periodicConformalGenerator5 v) = 0
  tt_orthogonal_gauge_gen :
    ∀ ε i,
      periodicEdgeInnerProduct5 (ttProjector ε) (periodicLongitudinalGaugeGenerator5 i) = 0
  reconstruct :
    ∀ ε e,
      conformalProjector ε e +
        periodicLongitudinalGaugeMap5 (gaugeCoeffProjector ε) e +
        ttProjector ε e = ε e

/-- Pure coefficient-projector data for the concrete longitudinal split.  The
conformal part is no longer an arbitrary map: it is explicitly generated from
encoded vertex-delta coefficients. -/
structure PeriodicTTLongitudinalCoefficientProjectorData5 where
  conformalCoeffProjector :
    PeriodicEdgePerturbation5 → Fin PeriodicTorus5.K.nV → ℝ
  gaugeCoeffProjector :
    PeriodicEdgePerturbation5 → PeriodicLongitudinalGaugeIdx5 → ℝ
  ttProjector : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  tt_orthogonal_conformal_gen :
    ∀ ε v, periodicEdgeInnerProduct5 (ttProjector ε) (periodicConformalGenerator5 v) = 0
  tt_orthogonal_gauge_gen :
    ∀ ε i,
      periodicEdgeInnerProduct5 (ttProjector ε) (periodicLongitudinalGaugeGenerator5 i) = 0
  reconstruct :
    ∀ ε e,
      periodicConformalGeneratorMap5 (conformalCoeffProjector ε) e +
        periodicLongitudinalGaugeMap5 (gaugeCoeffProjector ε) e +
        ttProjector ε e = ε e

/-- Residual after subtracting the conformal and longitudinal coefficient
projections from an edge perturbation. -/
def periodicLongitudinalCoefficientResidual5
    (conformalCoeffProjector :
      PeriodicEdgePerturbation5 → Fin PeriodicTorus5.K.nV → ℝ)
    (gaugeCoeffProjector :
      PeriodicEdgePerturbation5 → PeriodicLongitudinalGaugeIdx5 → ℝ)
    (ε : PeriodicEdgePerturbation5) : PeriodicEdgePerturbation5 :=
  fun e =>
    ε e - periodicConformalGeneratorMap5 (conformalCoeffProjector ε) e -
      periodicLongitudinalGaugeMap5 (gaugeCoeffProjector ε) e

/-- The coefficient solve can be stated with no separate TT projector: the TT
part is the residual after subtracting the conformal and longitudinal projections. -/
structure PeriodicTTLongitudinalCoefficientSolutionData5 where
  conformalCoeffProjector :
    PeriodicEdgePerturbation5 → Fin PeriodicTorus5.K.nV → ℝ
  gaugeCoeffProjector :
    PeriodicEdgePerturbation5 → PeriodicLongitudinalGaugeIdx5 → ℝ
  residual_orthogonal_conformal_gen :
    ∀ ε v,
      periodicEdgeInnerProduct5
        (periodicLongitudinalCoefficientResidual5
          conformalCoeffProjector gaugeCoeffProjector ε)
        (periodicConformalGenerator5 v) = 0
  residual_orthogonal_gauge_gen :
    ∀ ε i,
      periodicEdgeInnerProduct5
        (periodicLongitudinalCoefficientResidual5
          conformalCoeffProjector gaugeCoeffProjector ε)
        (periodicLongitudinalGaugeGenerator5 i) = 0

/-- Combined index for the fixed conformal vertex-delta generators and fixed
longitudinal vertex-vector generators. -/
abbrev PeriodicTTNormalEquationIdx5 :=
  Sum (Fin PeriodicTorus5.K.nV) PeriodicLongitudinalGaugeIdx5

/-- Translate a combined normal-equation generator index by a typed row base.
Conformal indices use the encoded vertex equivalence; gauge indices translate
the vertex and preserve the vector component. -/
noncomputable def periodicTranslateTTNormalEquationIdx5
    (base : PeriodicVertex5) :
    PeriodicTTNormalEquationIdx5 → PeriodicTTNormalEquationIdx5
  | Sum.inl v => Sum.inl (periodicTranslateEncodedVertexIdx5 base v)
  | Sum.inr i => Sum.inr (periodicTranslateLongitudinalGaugeIdx5 base i)

/-- Combined generator family for the concrete finite TT normal equations. -/
def periodicTTNormalEquationGenerator5
    (idx : PeriodicTTNormalEquationIdx5) : PeriodicEdgePerturbation5 :=
  match idx with
  | Sum.inl v => periodicConformalGenerator5 v
  | Sum.inr i => periodicLongitudinalGaugeGenerator5 i

/-- Conformal coefficients extracted from a combined coefficient vector. -/
def periodicTTNormalEquationConformalCoeff5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    Fin PeriodicTorus5.K.nV → ℝ :=
  fun v => coeff (Sum.inl v)

/-- Longitudinal coefficients extracted from a combined coefficient vector. -/
def periodicTTNormalEquationGaugeCoeff5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    PeriodicLongitudinalGaugeIdx5 → ℝ :=
  fun i => coeff (Sum.inr i)

/-- Combined generator map for the concrete finite TT normal equations. -/
def periodicTTNormalEquationGeneratorMap5 :
    (PeriodicTTNormalEquationIdx5 → ℝ) → PeriodicEdgePerturbation5 :=
  periodicGaugeGeneratorMap5 periodicTTNormalEquationGenerator5

/-- External-order displacement component used by the numerical TT
normal-equation generator matrix. -/
def periodicExternalDispCoordNat5 (disp : Fin 7) (component : Nat) : ℝ :=
  let bits := dispBits disp
  match component with
  | 0 => if bits.1 then 1 else 0
  | 1 => if bits.2.1 then 1 else 0
  | 2 => if bits.2.2 then 1 else 0
  | _ => 0

/-- External-order head vertex index for a typed edge. -/
def periodicExternalEdgeHeadIndex5 (e : PeriodicEdge5) : Nat :=
  periodicExternalVertexIndex5 e.endpoints.2

/-- Entry of the external TT normal-equation generator matrix used by the
Python payloads. Rows are external edge indices; columns `0..124` are
conformal vertex deltas and columns `125..499` are longitudinal
vertex-component generators. -/
def periodicExternalTTNormalEquationGeneratorMatrixEntry5
    (edgeIdx : Fin PeriodicTorus5.K.nE) (col : Nat) : ℝ :=
  let e := periodicExternalEdgeOfEncodedIdx5 edgeIdx
  let baseIdx := periodicExternalVertexIndex5 e.endpoints.1
  let headIdx := periodicExternalEdgeHeadIndex5 e
  if col < 125 then
    ((if col = baseIdx then 1 else 0) + (if col = headIdx then 1 else 0)) / 2
  else
    let gaugeCol := col - 125
    let vertexIdx := gaugeCol / 3
    let component := gaugeCol % 3
    (if vertexIdx = headIdx then periodicExternalDispCoordNat5 e.disp component else 0) -
      (if vertexIdx = baseIdx then periodicExternalDispCoordNat5 e.disp component else 0)

/-- External generator-matrix dot product for one selected row. This is the
Lean-side counterpart of the Python matrix dot used by generated certificate
skeletons. -/
def periodicExternalTTNormalEquationGeneratorMatrixDot5
    (coeff : Nat → ℝ) (edgeIdx : Fin PeriodicTorus5.K.nE) : ℝ :=
  ∑ col : Fin 500,
    coeff col.1 * periodicExternalTTNormalEquationGeneratorMatrixEntry5 edgeIdx col.1

/-- Sparse external generator-matrix dot product for one selected row. This is
definitionally small: two conformal endpoint terms plus the three possible
longitudinal component differences. -/
def periodicExternalTTNormalEquationGeneratorSparseDot5
    (coeff : Nat → ℝ) (edgeIdx : Fin PeriodicTorus5.K.nE) : ℝ :=
  let e := periodicExternalEdgeOfEncodedIdx5 edgeIdx
  let baseIdx := periodicExternalVertexIndex5 e.endpoints.1
  let headIdx := periodicExternalEdgeHeadIndex5 e
  (coeff baseIdx + coeff headIdx) / 2 +
    ((coeff (125 + 3 * headIdx + 0) -
        coeff (125 + 3 * baseIdx + 0)) *
      periodicExternalDispCoordNat5 e.disp 0) +
    ((coeff (125 + 3 * headIdx + 1) -
        coeff (125 + 3 * baseIdx + 1)) *
      periodicExternalDispCoordNat5 e.disp 1) +
    ((coeff (125 + 3 * headIdx + 2) -
        coeff (125 + 3 * baseIdx + 2)) *
      periodicExternalDispCoordNat5 e.disp 2)

/-- The combined normal-equation generator map splits into the already-fixed
conformal and longitudinal generator maps. -/
theorem periodicTTNormalEquationGeneratorMap5_eq_split
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) (e : PeriodicEdge5) :
    periodicTTNormalEquationGeneratorMap5 coeff e =
      periodicConformalGeneratorMap5
        (periodicTTNormalEquationConformalCoeff5 coeff) e +
      periodicLongitudinalGaugeMap5
        (periodicTTNormalEquationGaugeCoeff5 coeff) e := by
  classical
  unfold periodicTTNormalEquationGeneratorMap5 periodicConformalGeneratorMap5
    periodicLongitudinalGaugeMap5 periodicGaugeGeneratorMap5
    periodicTTNormalEquationConformalCoeff5 periodicTTNormalEquationGaugeCoeff5
    periodicTTNormalEquationGenerator5
  rw [Fintype.sum_sum_type]

/-- Right-hand side of the concrete TT normal equations: pair the input edge
perturbation with each combined generator. -/
def periodicTTNormalEquationLoad5
    (ε : PeriodicEdgePerturbation5) (idx : PeriodicTTNormalEquationIdx5) : ℝ :=
  periodicEdgeInnerProduct5 ε (periodicTTNormalEquationGenerator5 idx)

/-- Gram operator for the fixed combined conformal plus longitudinal generator
family. -/
def periodicTTNormalEquationGramApply5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ)
    (idx : PeriodicTTNormalEquationIdx5) : ℝ :=
  ∑ j : PeriodicTTNormalEquationIdx5,
    coeff j *
      periodicEdgeInnerProduct5
        (periodicTTNormalEquationGenerator5 idx)
        (periodicTTNormalEquationGenerator5 j)

/-- The Gram operator is exactly the inner product against the combined
generator map. -/
theorem periodicTTNormalEquationGramApply5_eq_inner_generatorMap
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ)
    (idx : PeriodicTTNormalEquationIdx5) :
    periodicTTNormalEquationGramApply5 coeff idx =
      periodicEdgeInnerProduct5
        (periodicTTNormalEquationGenerator5 idx)
        (periodicTTNormalEquationGeneratorMap5 coeff) := by
  unfold periodicTTNormalEquationGramApply5 periodicTTNormalEquationGeneratorMap5
    periodicGaugeGeneratorMap5
  rw [periodicEdgeInnerProduct5_linear_combo_right]

/-- Residual for a combined finite normal-equation coefficient projector. -/
def periodicTTNormalEquationResidual5
    (coeffProjector :
      PeriodicEdgePerturbation5 → PeriodicTTNormalEquationIdx5 → ℝ)
    (ε : PeriodicEdgePerturbation5) : PeriodicEdgePerturbation5 :=
  periodicLongitudinalCoefficientResidual5
    (fun ε => periodicTTNormalEquationConformalCoeff5 (coeffProjector ε))
    (fun ε => periodicTTNormalEquationGaugeCoeff5 (coeffProjector ε))
    ε

/-- The combined normal-equation residual is the input minus the combined
generator-map reconstruction. -/
theorem periodicTTNormalEquationResidual5_eq_sub_generatorMap
    (coeffProjector :
      PeriodicEdgePerturbation5 → PeriodicTTNormalEquationIdx5 → ℝ)
    (ε : PeriodicEdgePerturbation5) (e : PeriodicEdge5) :
    periodicTTNormalEquationResidual5 coeffProjector ε e =
      ε e - periodicTTNormalEquationGeneratorMap5 (coeffProjector ε) e := by
  unfold periodicTTNormalEquationResidual5 periodicLongitudinalCoefficientResidual5
  rw [periodicTTNormalEquationGeneratorMap5_eq_split]
  ring

/-- Pairing the combined residual with a generator is exactly load minus Gram. -/
theorem periodicTTNormalEquationResidual_inner_eq_load_sub_gram
    (coeffProjector :
      PeriodicEdgePerturbation5 → PeriodicTTNormalEquationIdx5 → ℝ)
    (ε : PeriodicEdgePerturbation5) (idx : PeriodicTTNormalEquationIdx5) :
    periodicEdgeInnerProduct5
      (periodicTTNormalEquationResidual5 coeffProjector ε)
      (periodicTTNormalEquationGenerator5 idx) =
      periodicTTNormalEquationLoad5 ε idx -
        periodicTTNormalEquationGramApply5 (coeffProjector ε) idx := by
  classical
  calc
    periodicEdgeInnerProduct5
        (periodicTTNormalEquationResidual5 coeffProjector ε)
        (periodicTTNormalEquationGenerator5 idx)
        =
        periodicEdgeInnerProduct5
          (fun e =>
            ε e - periodicTTNormalEquationGeneratorMap5 (coeffProjector ε) e)
          (periodicTTNormalEquationGenerator5 idx) := by
          unfold periodicEdgeInnerProduct5
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [periodicTTNormalEquationResidual5_eq_sub_generatorMap]
    _ =
        periodicTTNormalEquationLoad5 ε idx -
          periodicEdgeInnerProduct5
            (periodicTTNormalEquationGeneratorMap5 (coeffProjector ε))
            (periodicTTNormalEquationGenerator5 idx) := by
          unfold periodicEdgeInnerProduct5 periodicTTNormalEquationLoad5
          calc
            (∑ e : PeriodicEdge5,
                (fun e =>
                  ε e - periodicTTNormalEquationGeneratorMap5 (coeffProjector ε) e) e *
                  periodicTTNormalEquationGenerator5 idx e)
                =
                ∑ e : PeriodicEdge5,
                  (ε e * periodicTTNormalEquationGenerator5 idx e -
                    periodicTTNormalEquationGeneratorMap5 (coeffProjector ε) e *
                      periodicTTNormalEquationGenerator5 idx e) := by
                  refine Finset.sum_congr rfl ?_
                  intro e _
                  ring
            _ =
                (∑ e : PeriodicEdge5,
                  ε e * periodicTTNormalEquationGenerator5 idx e) -
                ∑ e : PeriodicEdge5,
                  periodicTTNormalEquationGeneratorMap5 (coeffProjector ε) e *
                    periodicTTNormalEquationGenerator5 idx e := by
                  rw [Finset.sum_sub_distrib]
    _ =
        periodicTTNormalEquationLoad5 ε idx -
          periodicEdgeInnerProduct5
            (periodicTTNormalEquationGenerator5 idx)
            (periodicTTNormalEquationGeneratorMap5 (coeffProjector ε)) := by
          rw [periodicEdgeInnerProduct5_symm]
    _ =
        periodicTTNormalEquationLoad5 ε idx -
          periodicTTNormalEquationGramApply5 (coeffProjector ε) idx := by
          rw [← periodicTTNormalEquationGramApply5_eq_inner_generatorMap]

/-- Single-system normal-equation data for the concrete finite TT split.  This is
the finite linear-algebra problem left by the decomposition track. -/
structure PeriodicTTNormalEquationSolutionData5 where
  coeffProjector :
    PeriodicEdgePerturbation5 → PeriodicTTNormalEquationIdx5 → ℝ
  normal_equations :
    ∀ ε idx,
      periodicEdgeInnerProduct5
        (periodicTTNormalEquationResidual5 coeffProjector ε)
        (periodicTTNormalEquationGenerator5 idx) = 0

/-- Explicit Gram-system solution data for the concrete finite TT split. -/
structure PeriodicTTGramSystemSolutionData5 where
  coeffProjector :
    PeriodicEdgePerturbation5 → PeriodicTTNormalEquationIdx5 → ℝ
  gram_system :
    ∀ ε idx,
      periodicTTNormalEquationGramApply5 (coeffProjector ε) idx =
        periodicTTNormalEquationLoad5 ε idx

/-- Load-solver data for the finite TT Gram operator.  This isolates the
remaining finite linear-algebra work: solve the Gram system for every load
vector arising from an edge perturbation. -/
structure PeriodicTTGramLoadSolverData5 where
  loadSolver :
    (PeriodicTTNormalEquationIdx5 → ℝ) → PeriodicTTNormalEquationIdx5 → ℝ
  solves_loads :
    ∀ ε idx,
      periodicTTNormalEquationGramApply5
          (loadSolver (periodicTTNormalEquationLoad5 ε)) idx =
        periodicTTNormalEquationLoad5 ε idx

/-- Image/range data for the finite TT Gram operator.  This is weaker and more
geometric than choosing a solver: every load generated by an edge perturbation
must lie in the image of the fixed Gram operator. -/
structure PeriodicTTGramLoadImageData5 where
  load_mem_image :
    ∀ ε,
      ∃ coeff : PeriodicTTNormalEquationIdx5 → ℝ,
        ∀ idx,
          periodicTTNormalEquationGramApply5 coeff idx =
            periodicTTNormalEquationLoad5 ε idx

/-- Coefficient-space inner product on the finite normal-equation index set. -/
def periodicTTNormalEquationCoeffInnerProduct5
    (a b : PeriodicTTNormalEquationIdx5 → ℝ) : ℝ :=
  ∑ idx : PeriodicTTNormalEquationIdx5, a idx * b idx

/-- Coefficient-vector space for the combined conformal plus longitudinal normal
equations. -/
abbrev PeriodicTTCoeffSpace5 :=
  PeriodicTTNormalEquationIdx5 → ℝ

/-- `WithLp 2` Hilbert wrapper for the finite coefficient-vector space.  The raw
coefficient type intentionally stays a function space elsewhere in the file;
this wrapper imports Mathlib's inner-product range theorem without changing the
public TT data surfaces. -/
abbrev PeriodicTTCoeffHilbertSpace5 :=
  WithLp 2 PeriodicTTCoeffSpace5

/-- Linear equivalence between the Hilbert wrapper and the raw coefficient
function space. -/
noncomputable abbrev periodicTTCoeffHilbertEquiv5 :
    PeriodicTTCoeffHilbertSpace5 ≃ₗ[ℝ] PeriodicTTCoeffSpace5 :=
  WithLp.linearEquiv 2 ℝ PeriodicTTCoeffSpace5

/-- Gram operator as a coefficient vector. -/
def periodicTTNormalEquationGramVector5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    PeriodicTTNormalEquationIdx5 → ℝ :=
  fun idx => periodicTTNormalEquationGramApply5 coeff idx

/-- The TT Gram operator as a linear map on raw coefficient functions. -/
noncomputable def periodicTTGramLinearMap5 :
    PeriodicTTCoeffSpace5 →ₗ[ℝ] PeriodicTTCoeffSpace5 where
  toFun := periodicTTNormalEquationGramVector5
  map_add' := by
    intro a b
    funext idx
    unfold periodicTTNormalEquationGramVector5 periodicTTNormalEquationGramApply5
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    funext idx
    unfold periodicTTNormalEquationGramVector5 periodicTTNormalEquationGramApply5
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring

/-- The TT Gram operator transported to Mathlib's finite Hilbert wrapper. -/
noncomputable def periodicTTGramHilbertLinearMap5 :
    PeriodicTTCoeffHilbertSpace5 →ₗ[ℝ] PeriodicTTCoeffHilbertSpace5 :=
  periodicTTCoeffHilbertEquiv5.symm.toLinearMap.comp
    (periodicTTGramLinearMap5.comp periodicTTCoeffHilbertEquiv5.toLinearMap)

/-- The Hilbert-wrapper inner product is the coefficient-space dot product. -/
theorem periodicTTCoeffHilbert_inner_eq_coeffInnerProduct5
    (a b : PeriodicTTCoeffSpace5) :
    inner ℝ
      (periodicTTCoeffHilbertEquiv5.symm a)
      (periodicTTCoeffHilbertEquiv5.symm b) =
      periodicTTNormalEquationCoeffInnerProduct5 a b := by
  simp [periodicTTNormalEquationCoeffInnerProduct5, PiLp.inner_apply, mul_comm]

/-- Symmetry of the coefficient-space dot product. -/
theorem periodicTTNormalEquationCoeffInnerProduct5_symm
    (a b : PeriodicTTCoeffSpace5) :
    periodicTTNormalEquationCoeffInnerProduct5 a b =
      periodicTTNormalEquationCoeffInnerProduct5 b a := by
  unfold periodicTTNormalEquationCoeffInnerProduct5
  refine Finset.sum_congr rfl ?_
  intro idx _
  ring

/-- Symmetric Gram entry identity for the combined generator family. -/
theorem periodicTTNormalEquationGramEntry_symm5
    (i j : PeriodicTTNormalEquationIdx5) :
    periodicEdgeInnerProduct5
      (periodicTTNormalEquationGenerator5 i)
      (periodicTTNormalEquationGenerator5 j) =
    periodicEdgeInnerProduct5
      (periodicTTNormalEquationGenerator5 j)
      (periodicTTNormalEquationGenerator5 i) :=
  periodicEdgeInnerProduct5_symm _ _

/-- The finite TT Gram operator is self-adjoint for the coefficient inner
product. -/
theorem periodicTTNormalEquationGram_selfAdjoint5
    (a b : PeriodicTTNormalEquationIdx5 → ℝ) :
    periodicTTNormalEquationCoeffInnerProduct5
      (periodicTTNormalEquationGramVector5 a) b =
    periodicTTNormalEquationCoeffInnerProduct5
      a (periodicTTNormalEquationGramVector5 b) := by
  classical
  unfold periodicTTNormalEquationCoeffInnerProduct5
    periodicTTNormalEquationGramVector5 periodicTTNormalEquationGramApply5
  calc
    (∑ i : PeriodicTTNormalEquationIdx5,
        (∑ j : PeriodicTTNormalEquationIdx5,
          a j *
            periodicEdgeInnerProduct5
              (periodicTTNormalEquationGenerator5 i)
              (periodicTTNormalEquationGenerator5 j)) * b i)
        =
        ∑ i : PeriodicTTNormalEquationIdx5,
          ∑ j : PeriodicTTNormalEquationIdx5,
            a j * b i *
              periodicEdgeInnerProduct5
                (periodicTTNormalEquationGenerator5 i)
                (periodicTTNormalEquationGenerator5 j) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ =
        ∑ j : PeriodicTTNormalEquationIdx5,
          ∑ i : PeriodicTTNormalEquationIdx5,
            a j * b i *
              periodicEdgeInnerProduct5
                (periodicTTNormalEquationGenerator5 i)
                (periodicTTNormalEquationGenerator5 j) := by
          rw [Finset.sum_comm]
    _ =
        ∑ j : PeriodicTTNormalEquationIdx5,
          ∑ i : PeriodicTTNormalEquationIdx5,
            a j * b i *
              periodicEdgeInnerProduct5
                (periodicTTNormalEquationGenerator5 j)
                (periodicTTNormalEquationGenerator5 i) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [periodicTTNormalEquationGramEntry_symm5 i j]
    _ =
        ∑ j : PeriodicTTNormalEquationIdx5,
          a j *
            ∑ i : PeriodicTTNormalEquationIdx5,
              b i *
                periodicEdgeInnerProduct5
                  (periodicTTNormalEquationGenerator5 j)
                  (periodicTTNormalEquationGenerator5 i) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring

set_option maxRecDepth 20000

/-- The transported finite TT Gram operator is symmetric in Mathlib's Hilbert
wrapper. -/
theorem periodicTTGramHilbertLinearMap_isSymmetric5 :
    LinearMap.IsSymmetric periodicTTGramHilbertLinearMap5 := by
  intro x y
  unfold periodicTTGramHilbertLinearMap5
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show
      inner ℝ
        (periodicTTCoeffHilbertEquiv5.symm
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 x))) y =
        periodicTTNormalEquationCoeffInnerProduct5
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 x))
          (periodicTTCoeffHilbertEquiv5 y) by
      simpa using
        periodicTTCoeffHilbert_inner_eq_coeffInnerProduct5
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 x))
          (periodicTTCoeffHilbertEquiv5 y)]
  rw [show
      inner ℝ x
        (periodicTTCoeffHilbertEquiv5.symm
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 y))) =
        periodicTTNormalEquationCoeffInnerProduct5
          (periodicTTCoeffHilbertEquiv5 x)
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 y)) by
      simpa using
        periodicTTCoeffHilbert_inner_eq_coeffInnerProduct5
          (periodicTTCoeffHilbertEquiv5 x)
          (periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 y))]
  exact
    periodicTTNormalEquationGram_selfAdjoint5
      (periodicTTCoeffHilbertEquiv5 x)
      (periodicTTCoeffHilbertEquiv5 y)

/-- Kernel of the finite TT Gram operator. -/
def periodicTTGramKernel5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) : Prop :=
  ∀ idx, periodicTTNormalEquationGramApply5 coeff idx = 0

/-- A Gram-kernel coefficient vector generates the zero edge perturbation. -/
theorem periodicTTGramKernel_generatorMap_zero5
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ)
    (hkernel : periodicTTGramKernel5 coeff) :
    periodicTTNormalEquationGeneratorMap5 coeff = fun _ => 0 := by
  apply periodicEdgePerturbation5_eq_zero_of_inner_self_eq_zero
  calc
    periodicEdgeInnerProduct5
        (periodicTTNormalEquationGeneratorMap5 coeff)
        (periodicTTNormalEquationGeneratorMap5 coeff)
        =
        periodicEdgeInnerProduct5
          (periodicTTNormalEquationGeneratorMap5 coeff)
          (fun e =>
            ∑ idx : PeriodicTTNormalEquationIdx5,
              coeff idx * periodicTTNormalEquationGenerator5 idx e) := by
          rfl
    _ =
        ∑ idx : PeriodicTTNormalEquationIdx5,
          coeff idx *
            periodicEdgeInnerProduct5
              (periodicTTNormalEquationGeneratorMap5 coeff)
              (periodicTTNormalEquationGenerator5 idx) := by
          rw [periodicEdgeInnerProduct5_linear_combo_right]
    _ =
        ∑ idx : PeriodicTTNormalEquationIdx5,
          coeff idx *
            periodicEdgeInnerProduct5
              (periodicTTNormalEquationGenerator5 idx)
              (periodicTTNormalEquationGeneratorMap5 coeff) := by
          refine Finset.sum_congr rfl ?_
          intro idx _
          rw [periodicEdgeInnerProduct5_symm]
    _ =
        ∑ idx : PeriodicTTNormalEquationIdx5,
          coeff idx * periodicTTNormalEquationGramApply5 coeff idx := by
          refine Finset.sum_congr rfl ?_
          intro idx _
          rw [periodicTTNormalEquationGramApply5_eq_inner_generatorMap]
    _ = ∑ idx : PeriodicTTNormalEquationIdx5, coeff idx * 0 := by
          refine Finset.sum_congr rfl ?_
          intro idx _
          rw [hkernel idx, mul_zero]
    _ = 0 := by
          simp

/-- The load induced by an edge perturbation annihilates every Gram-kernel
coefficient vector. -/
def periodicTTLoadAnnihilatesGramKernel5
    (ε : PeriodicEdgePerturbation5) : Prop :=
  ∀ kernelCoeff,
    periodicTTGramKernel5 kernelCoeff →
      periodicTTNormalEquationCoeffInnerProduct5
        (periodicTTNormalEquationLoad5 ε) kernelCoeff = 0

/-- Pairing the load vector with coefficients is the edge inner product against
the combined generated mode. -/
theorem periodicTTLoadCoeffInnerProduct_eq_inner_generatorMap5
    (ε : PeriodicEdgePerturbation5)
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    periodicTTNormalEquationCoeffInnerProduct5
      (periodicTTNormalEquationLoad5 ε) coeff =
      periodicEdgeInnerProduct5 ε (periodicTTNormalEquationGeneratorMap5 coeff) := by
  classical
  unfold periodicTTNormalEquationCoeffInnerProduct5 periodicTTNormalEquationLoad5
    periodicTTNormalEquationGeneratorMap5 periodicGaugeGeneratorMap5
  rw [periodicEdgeInnerProduct5_linear_combo_right]
  refine Finset.sum_congr rfl ?_
  intro idx _
  ring

/-- A longitudinal TT perturbation is orthogonal to every combined conformal
plus longitudinal normal-equation generator map. -/
theorem periodicLongitudinalTTSubspace5_inner_generatorMap_eq_zero
    (ε : PeriodicEdgePerturbation5)
    (hε :
      PeriodicTTOrthogonal5
        (PeriodicLongitudinalGaugeIdx5 → ℝ)
        periodicLongitudinalGaugeMap5 ε)
    (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    periodicEdgeInnerProduct5 ε
      (periodicTTNormalEquationGeneratorMap5 coeff) = 0 := by
  let cCoeff := periodicTTNormalEquationConformalCoeff5 coeff
  let gCoeff := periodicTTNormalEquationGaugeCoeff5 coeff
  have hmap :
      periodicTTNormalEquationGeneratorMap5 coeff =
        fun e =>
          periodicConformalGeneratorMap5 cCoeff e +
            periodicLongitudinalGaugeMap5 gCoeff e := by
    funext e
    exact periodicTTNormalEquationGeneratorMap5_eq_split coeff e
  rw [hmap]
  rw [periodicEdgeInnerProduct5_add_right]
  have hc :
      periodicEdgeInnerProduct5 ε
        (periodicConformalGeneratorMap5 cCoeff) = 0 :=
    hε.1 (periodicConformalGeneratorMap5 cCoeff)
      (periodicConformalGeneratorMap5_mem cCoeff)
  have hg :
      periodicEdgeInnerProduct5 ε
        (periodicLongitudinalGaugeMap5 gCoeff) = 0 :=
    hε.2 (periodicLongitudinalGaugeMap5 gCoeff) ⟨gCoeff, rfl⟩
  rw [hc, hg]
  ring

/-- Kernel-criterion data for the finite TT Gram operator.  This is the finite
Fredholm-alternative surface: to prove the loads are in the Gram image, it is
enough to prove they annihilate the Gram kernel, together with the finite
range criterion for this fixed Gram operator. -/
structure PeriodicTTGramKernelCriterionData5 where
  range_of_kernel_orthogonal :
    ∀ load : PeriodicTTNormalEquationIdx5 → ℝ,
      (∀ kernelCoeff,
        periodicTTGramKernel5 kernelCoeff →
          periodicTTNormalEquationCoeffInnerProduct5 load kernelCoeff = 0) →
        ∃ coeff : PeriodicTTNormalEquationIdx5 → ℝ,
          ∀ idx, periodicTTNormalEquationGramApply5 coeff idx = load idx
  loads_annihilate_kernel :
    ∀ ε, periodicTTLoadAnnihilatesGramKernel5 ε

/-- Kernel-zero-mode data for the TT Gram operator.  This leaves only the finite
range criterion plus the statement that every Gram-kernel coefficient vector
generates the zero edge perturbation. -/
structure PeriodicTTGramKernelGeneratorMapZeroData5 where
  range_of_kernel_orthogonal :
    ∀ load : PeriodicTTNormalEquationIdx5 → ℝ,
      (∀ kernelCoeff,
        periodicTTGramKernel5 kernelCoeff →
          periodicTTNormalEquationCoeffInnerProduct5 load kernelCoeff = 0) →
        ∃ coeff : PeriodicTTNormalEquationIdx5 → ℝ,
          ∀ idx, periodicTTNormalEquationGramApply5 coeff idx = load idx
  kernel_generatorMap_zero :
    ∀ coeff,
      periodicTTGramKernel5 coeff →
        periodicTTNormalEquationGeneratorMap5 coeff = fun _ => 0

/-- Range-criterion data for the finite TT Gram operator.  Since Gram-kernel
coefficient vectors now theorematically generate the zero edge perturbation, the
only remaining finite-algebra input is this range/Fredholm criterion for the
fixed Gram operator. -/
structure PeriodicTTGramRangeCriterionData5 where
  range_of_kernel_orthogonal :
    ∀ load : PeriodicTTNormalEquationIdx5 → ℝ,
      (∀ kernelCoeff,
        periodicTTGramKernel5 kernelCoeff →
          periodicTTNormalEquationCoeffInnerProduct5 load kernelCoeff = 0) →
        ∃ coeff : PeriodicTTNormalEquationIdx5 → ℝ,
          ∀ idx, periodicTTNormalEquationGramApply5 coeff idx = load idx

/-- The fixed finite TT Gram range/Fredholm criterion is theorem-level.  This is
the finite-dimensional fact that a load orthogonal to the Gram kernel lies in
the range of the self-adjoint Gram operator. -/
theorem periodicTTGramRangeCriterionData5_proved :
    PeriodicTTGramRangeCriterionData5 := by
  refine ⟨?_⟩
  intro load hload
  let loadH : PeriodicTTCoeffHilbertSpace5 :=
    periodicTTCoeffHilbertEquiv5.symm load
  have hkerOrth :
      loadH ∈ (LinearMap.ker periodicTTGramHilbertLinearMap5)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hraw_zero :
        periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 u) = 0 := by
      have hcongr := congrArg periodicTTCoeffHilbertEquiv5 hu
      simpa [periodicTTGramHilbertLinearMap5] using hcongr
    have hkernel :
        periodicTTGramKernel5 (periodicTTCoeffHilbertEquiv5 u) := by
      intro idx
      have hidx := congrFun hraw_zero idx
      simpa [periodicTTGramLinearMap5, periodicTTNormalEquationGramVector5] using hidx
    have hcustom :
        periodicTTNormalEquationCoeffInnerProduct5
          load (periodicTTCoeffHilbertEquiv5 u) = 0 :=
      hload (periodicTTCoeffHilbertEquiv5 u) hkernel
    calc
      inner ℝ u loadH =
          periodicTTNormalEquationCoeffInnerProduct5
            (periodicTTCoeffHilbertEquiv5 u) load := by
        simpa [loadH] using
          periodicTTCoeffHilbert_inner_eq_coeffInnerProduct5
            (periodicTTCoeffHilbertEquiv5 u) load
      _ =
          periodicTTNormalEquationCoeffInnerProduct5
            load (periodicTTCoeffHilbertEquiv5 u) :=
        periodicTTNormalEquationCoeffInnerProduct5_symm
          (periodicTTCoeffHilbertEquiv5 u) load
      _ = 0 := hcustom
  have horthRange :
      (LinearMap.range periodicTTGramHilbertLinearMap5)ᗮ =
        LinearMap.ker periodicTTGramHilbertLinearMap5 :=
    LinearMap.IsSymmetric.orthogonal_range periodicTTGramHilbertLinearMap_isSymmetric5
  have hmemDouble :
      loadH ∈ (LinearMap.range periodicTTGramHilbertLinearMap5)ᗮᗮ := by
    simpa [horthRange] using hkerOrth
  have hdouble :
      (LinearMap.range periodicTTGramHilbertLinearMap5)ᗮᗮ =
        LinearMap.range periodicTTGramHilbertLinearMap5 := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.topologicalClosure_eq_self
      (LinearMap.range periodicTTGramHilbertLinearMap5)
  have hmemRange :
      loadH ∈ LinearMap.range periodicTTGramHilbertLinearMap5 := by
    simpa [hdouble] using hmemDouble
  rcases LinearMap.mem_range.mp hmemRange with ⟨coeffH, hcoeffH⟩
  refine ⟨periodicTTCoeffHilbertEquiv5 coeffH, ?_⟩
  intro idx
  have hraw :
      periodicTTGramLinearMap5 (periodicTTCoeffHilbertEquiv5 coeffH) = load := by
    have hcongr := congrArg periodicTTCoeffHilbertEquiv5 hcoeffH
    simpa [periodicTTGramHilbertLinearMap5, loadH] using hcongr
  have hidx := congrFun hraw idx
  simpa [periodicTTGramLinearMap5, periodicTTNormalEquationGramVector5] using hidx

/-- Generator-map projector data is gauge-generator projector data for the gauge
map induced by the same generator family. -/
def PeriodicTTGaugeGeneratorProjectorData5.ofGeneratorMapData
    {GIdx : Type} [Fintype GIdx]
    (D : PeriodicTTGeneratorMapProjectorData5 GIdx) :
    PeriodicTTGaugeGeneratorProjectorData5
      (GIdx → ℝ) (periodicGaugeGeneratorMap5 D.gaugeGen) GIdx where
  conformalProjector := D.conformalProjector
  gaugeProjector := fun ε => periodicGaugeGeneratorMap5 D.gaugeGen (D.gaugeCoeffProjector ε)
  ttProjector := D.ttProjector
  gaugeGen := D.gaugeGen
  conformal_mem := D.conformal_mem
  gauge_mem := by
    intro ε
    exact ⟨D.gaugeCoeffProjector ε, rfl⟩
  gauge_span := periodicGaugeSubspace5_spanned_by_generatorMap D.gaugeGen
  tt_orthogonal_conformal_gen := D.tt_orthogonal_conformal_gen
  tt_orthogonal_gauge_gen := D.tt_orthogonal_gauge_gen
  reconstruct := D.reconstruct

/-- Concrete longitudinal projector data is generator-map projector data for the
longitudinal vertex-vector basis. -/
def PeriodicTTGeneratorMapProjectorData5.ofLongitudinalData
    (D : PeriodicTTLongitudinalProjectorData5) :
    PeriodicTTGeneratorMapProjectorData5 PeriodicLongitudinalGaugeIdx5 where
  conformalProjector := D.conformalProjector
  gaugeCoeffProjector := D.gaugeCoeffProjector
  ttProjector := D.ttProjector
  gaugeGen := periodicLongitudinalGaugeGenerator5
  conformal_mem := D.conformal_mem
  tt_orthogonal_conformal_gen := D.tt_orthogonal_conformal_gen
  tt_orthogonal_gauge_gen := D.tt_orthogonal_gauge_gen
  reconstruct := by
    intro ε e
    exact D.reconstruct ε e

/-- Coefficient-projector data supplies the concrete longitudinal projector data
by generating the conformal part from encoded vertex-delta coefficients. -/
def PeriodicTTLongitudinalProjectorData5.ofCoefficientData
    (D : PeriodicTTLongitudinalCoefficientProjectorData5) :
    PeriodicTTLongitudinalProjectorData5 where
  conformalProjector := fun ε => periodicConformalGeneratorMap5 (D.conformalCoeffProjector ε)
  gaugeCoeffProjector := D.gaugeCoeffProjector
  ttProjector := D.ttProjector
  conformal_mem := fun ε => periodicConformalGeneratorMap5_mem (D.conformalCoeffProjector ε)
  tt_orthogonal_conformal_gen := D.tt_orthogonal_conformal_gen
  tt_orthogonal_gauge_gen := D.tt_orthogonal_gauge_gen
  reconstruct := D.reconstruct

/-- Residual-defined coefficient-solution data supplies the coefficient-projector
data expected by the decomposition target. -/
def PeriodicTTLongitudinalCoefficientProjectorData5.ofSolutionData
    (D : PeriodicTTLongitudinalCoefficientSolutionData5) :
    PeriodicTTLongitudinalCoefficientProjectorData5 where
  conformalCoeffProjector := D.conformalCoeffProjector
  gaugeCoeffProjector := D.gaugeCoeffProjector
  ttProjector :=
    periodicLongitudinalCoefficientResidual5
      D.conformalCoeffProjector D.gaugeCoeffProjector
  tt_orthogonal_conformal_gen := D.residual_orthogonal_conformal_gen
  tt_orthogonal_gauge_gen := D.residual_orthogonal_gauge_gen
  reconstruct := by
    intro ε e
    unfold periodicLongitudinalCoefficientResidual5
    ring

/-- A solution of the combined normal equations supplies the residual-defined
coefficient solution data. -/
def PeriodicTTLongitudinalCoefficientSolutionData5.ofNormalEquationData
    (D : PeriodicTTNormalEquationSolutionData5) :
    PeriodicTTLongitudinalCoefficientSolutionData5 where
  conformalCoeffProjector :=
    fun ε => periodicTTNormalEquationConformalCoeff5 (D.coeffProjector ε)
  gaugeCoeffProjector :=
    fun ε => periodicTTNormalEquationGaugeCoeff5 (D.coeffProjector ε)
  residual_orthogonal_conformal_gen := by
    intro ε v
    simpa [periodicTTNormalEquationResidual5, periodicTTNormalEquationGenerator5]
      using D.normal_equations ε (Sum.inl v)
  residual_orthogonal_gauge_gen := by
    intro ε i
    simpa [periodicTTNormalEquationResidual5, periodicTTNormalEquationGenerator5]
      using D.normal_equations ε (Sum.inr i)

/-- Solving the explicit Gram system supplies the combined normal equations. -/
def PeriodicTTNormalEquationSolutionData5.ofGramSystemData
    (D : PeriodicTTGramSystemSolutionData5) :
    PeriodicTTNormalEquationSolutionData5 where
  coeffProjector := D.coeffProjector
  normal_equations := by
    intro ε idx
    rw [periodicTTNormalEquationResidual_inner_eq_load_sub_gram]
    rw [D.gram_system ε idx]
    ring

/-- A load solver supplies the explicit Gram-system solution data. -/
def PeriodicTTGramSystemSolutionData5.ofLoadSolverData
    (D : PeriodicTTGramLoadSolverData5) :
    PeriodicTTGramSystemSolutionData5 where
  coeffProjector := fun ε => D.loadSolver (periodicTTNormalEquationLoad5 ε)
  gram_system := D.solves_loads

/-- Load-image data supplies a solver on the physical load subspace by choosing a
preimage for each load that actually occurs. -/
noncomputable def PeriodicTTGramLoadSolverData5.ofLoadImageData
    (D : PeriodicTTGramLoadImageData5) :
    PeriodicTTGramLoadSolverData5 where
  loadSolver := by
    classical
    exact fun load =>
      if h : ∃ ε, load = periodicTTNormalEquationLoad5 ε then
        Classical.choose (D.load_mem_image (Classical.choose h))
      else
        fun _ => 0
  solves_loads := by
    intro ε idx
    classical
    let h : ∃ η, periodicTTNormalEquationLoad5 ε = periodicTTNormalEquationLoad5 η :=
      ⟨ε, rfl⟩
    rw [dif_pos h]
    have hload :
        periodicTTNormalEquationLoad5 ε =
          periodicTTNormalEquationLoad5 (Classical.choose h) :=
      Classical.choose_spec h
    exact
      (Classical.choose_spec (D.load_mem_image (Classical.choose h)) idx).trans
        ((congrFun hload idx).symm)

/-- The kernel criterion supplies the load-image data required by the finite TT
decomposition target. -/
def PeriodicTTGramLoadImageData5.ofKernelCriterionData
    (D : PeriodicTTGramKernelCriterionData5) :
    PeriodicTTGramLoadImageData5 where
  load_mem_image := by
    intro ε
    exact D.range_of_kernel_orthogonal
      (periodicTTNormalEquationLoad5 ε)
      (D.loads_annihilate_kernel ε)

/-- Kernel-generator-zero data supplies the finite Gram-kernel criterion. -/
def PeriodicTTGramKernelCriterionData5.ofKernelGeneratorMapZeroData
    (D : PeriodicTTGramKernelGeneratorMapZeroData5) :
    PeriodicTTGramKernelCriterionData5 where
  range_of_kernel_orthogonal := D.range_of_kernel_orthogonal
  loads_annihilate_kernel := by
    intro ε kernelCoeff hkernel
    rw [periodicTTLoadCoeffInnerProduct_eq_inner_generatorMap5]
    rw [D.kernel_generatorMap_zero kernelCoeff hkernel]
    exact periodicEdgeInnerProduct5_zero_right ε

/-- The finite Gram range criterion alone now supplies the Gram-kernel criterion,
because Gram-kernel coefficients are proved to generate zero edge perturbations. -/
def PeriodicTTGramKernelCriterionData5.ofRangeCriterionData
    (D : PeriodicTTGramRangeCriterionData5) :
    PeriodicTTGramKernelCriterionData5 where
  range_of_kernel_orthogonal := D.range_of_kernel_orthogonal
  loads_annihilate_kernel := by
    intro ε kernelCoeff hkernel
    rw [periodicTTLoadCoeffInnerProduct_eq_inner_generatorMap5]
    rw [periodicTTGramKernel_generatorMap_zero5 kernelCoeff hkernel]
    exact periodicEdgeInnerProduct5_zero_right ε

/-- Gauge-generator data is full finite-generator data, using encoded vertex
delta generators for the conformal slice. -/
def PeriodicTTFiniteGeneratorProjectorData5.ofGaugeGeneratorData
    {GaugePotential GIdx : Type} [Fintype GIdx]
    {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTGaugeGeneratorProjectorData5 GaugePotential gaugeMap GIdx) :
    PeriodicTTFiniteGeneratorProjectorData5
      GaugePotential gaugeMap (Fin PeriodicTorus5.K.nV) GIdx where
  conformalProjector := D.conformalProjector
  gaugeProjector := D.gaugeProjector
  ttProjector := D.ttProjector
  conformalGen := periodicConformalGenerator5
  gaugeGen := D.gaugeGen
  conformal_mem := D.conformal_mem
  gauge_mem := D.gauge_mem
  conformal_span := periodicConformalLogSubspace5_spanned_by_encodedVertexGenerators
  gauge_span := D.gauge_span
  tt_orthogonal_conformal_gen := D.tt_orthogonal_conformal_gen
  tt_orthogonal_gauge_gen := D.tt_orthogonal_gauge_gen
  reconstruct := D.reconstruct

/-- Orthogonality to finite spanning generators gives full TT orthogonality. -/
theorem periodicTTOrthogonal5_of_generator_orthogonality
    {GaugePotential CIdx GIdx : Type} [Fintype CIdx] [Fintype GIdx]
    {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTFiniteGeneratorProjectorData5 GaugePotential gaugeMap CIdx GIdx)
    (ε : PeriodicEdgePerturbation5) :
    PeriodicTTOrthogonal5 GaugePotential gaugeMap (D.ttProjector ε) := by
  constructor
  · intro c hc
    rcases D.conformal_span c hc with ⟨coeff, hcoeff⟩
    have hc_eq : c = fun e => ∑ i : CIdx, coeff i * D.conformalGen i e := by
      funext e
      exact hcoeff e
    rw [hc_eq, periodicEdgeInnerProduct5_linear_combo_right]
    simp [D.tt_orthogonal_conformal_gen ε]
  · intro g hg
    rcases D.gauge_span g hg with ⟨coeff, hcoeff⟩
    have hg_eq : g = fun e => ∑ i : GIdx, coeff i * D.gaugeGen i e := by
      funext e
      exact hcoeff e
    rw [hg_eq, periodicEdgeInnerProduct5_linear_combo_right]
    simp [D.tt_orthogonal_gauge_gen ε]

/-- Finite-generator projector data supplies the projector data consumed by the
orthogonal decomposition theorem. -/
def PeriodicTTProjectorData5.ofFiniteGeneratorData
    {GaugePotential CIdx GIdx : Type} [Fintype CIdx] [Fintype GIdx]
    {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTFiniteGeneratorProjectorData5 GaugePotential gaugeMap CIdx GIdx) :
    PeriodicTTProjectorData5 GaugePotential gaugeMap where
  conformalProjector := D.conformalProjector
  gaugeProjector := D.gaugeProjector
  ttProjector := D.ttProjector
  conformal_mem := D.conformal_mem
  gauge_mem := D.gauge_mem
  tt_mem := periodicTTOrthogonal5_of_generator_orthogonality D
  reconstruct := D.reconstruct

/-- Projector data induces the raw additive splitting expected by the earlier
Track 1.D decomposition target. -/
def PeriodicTTProjectorData5.toRawSplitting
    {GaugePotential : Type} {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTProjectorData5 GaugePotential gaugeMap) :
    RawEdgePerturbationSplitting PeriodicEdge5 where
  conformalPart := D.conformalProjector
  gaugePart := D.gaugeProjector
  ttPart := D.ttProjector
  reconstruct := D.reconstruct

/-- Projector data closes the finite orthogonal conformal/gauge/TT decomposition
target.  This is the intended next consumption theorem for a concrete periodic
Freudenthal projector construction. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_projectorData
    {GaugePotential : Type} {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTProjectorData5 GaugePotential gaugeMap) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5 GaugePotential gaugeMap := by
  refine ⟨D.toRawSplitting, ?_, ?_, ?_⟩
  · exact D.conformal_mem
  · exact D.gauge_mem
  · exact D.tt_mem

/-- Finite-generator projector data closes the finite orthogonal decomposition
target.  The remaining tensor-lane task is now concrete: produce the generators,
solve the projector system, and prove reconstruction. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_finiteGeneratorData
    {GaugePotential CIdx GIdx : Type} [Fintype CIdx] [Fintype GIdx]
    {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTFiniteGeneratorProjectorData5 GaugePotential gaugeMap CIdx GIdx) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5 GaugePotential gaugeMap :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_projectorData
    (PeriodicTTProjectorData5.ofFiniteGeneratorData D)

/-- Gauge-generator projector data closes the finite orthogonal decomposition
target, because the conformal generators are fixed and already span. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gaugeGeneratorData
    {GaugePotential GIdx : Type} [Fintype GIdx]
    {gaugeMap : GaugePotential → PeriodicEdgePerturbation5}
    (D : PeriodicTTGaugeGeneratorProjectorData5 GaugePotential gaugeMap GIdx) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5 GaugePotential gaugeMap :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_finiteGeneratorData
    (PeriodicTTFiniteGeneratorProjectorData5.ofGaugeGeneratorData D)

/-- Generator-map projector data closes the finite orthogonal decomposition
target for the gauge map generated by its own finite basis. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_generatorMapData
    {GIdx : Type} [Fintype GIdx]
    (D : PeriodicTTGeneratorMapProjectorData5 GIdx) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (GIdx → ℝ) (periodicGaugeGeneratorMap5 D.gaugeGen) :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gaugeGeneratorData
    (PeriodicTTGaugeGeneratorProjectorData5.ofGeneratorMapData D)

/-- Concrete longitudinal projector data closes the finite TT decomposition
target for the vertex-vector longitudinal gauge map. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalData
    (D : PeriodicTTLongitudinalProjectorData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 := by
  exact periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_generatorMapData
    (PeriodicTTGeneratorMapProjectorData5.ofLongitudinalData D)

/-- Pure coefficient-projector data closes the concrete longitudinal TT
decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalCoefficientData
    (D : PeriodicTTLongitudinalCoefficientProjectorData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalData
    (PeriodicTTLongitudinalProjectorData5.ofCoefficientData D)

/-- Residual-defined coefficient-solution data closes the concrete longitudinal
TT decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalCoefficientSolutionData
    (D : PeriodicTTLongitudinalCoefficientSolutionData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalCoefficientData
    (PeriodicTTLongitudinalCoefficientProjectorData5.ofSolutionData D)

/-- A solution of the combined finite normal equations closes the concrete
longitudinal TT decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_normalEquationData
    (D : PeriodicTTNormalEquationSolutionData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_longitudinalCoefficientSolutionData
    (PeriodicTTLongitudinalCoefficientSolutionData5.ofNormalEquationData D)

/-- A solution of the explicit finite Gram system closes the concrete
longitudinal TT decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramSystemData
    (D : PeriodicTTGramSystemSolutionData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_normalEquationData
    (PeriodicTTNormalEquationSolutionData5.ofGramSystemData D)

/-- A finite load solver for the TT Gram operator closes the concrete
longitudinal TT decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramLoadSolverData
    (D : PeriodicTTGramLoadSolverData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramSystemData
    (PeriodicTTGramSystemSolutionData5.ofLoadSolverData D)

/-- If every physical load lies in the Gram image, the concrete longitudinal TT
decomposition target closes. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramLoadImageData
    (D : PeriodicTTGramLoadImageData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramLoadSolverData
    (PeriodicTTGramLoadSolverData5.ofLoadImageData D)

/-- The finite Gram-kernel criterion closes the concrete longitudinal TT
decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramKernelCriterionData
    (D : PeriodicTTGramKernelCriterionData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramLoadImageData
    (PeriodicTTGramLoadImageData5.ofKernelCriterionData D)

/-- If Gram-kernel coefficient vectors generate zero edge perturbations, then the
finite Gram-kernel criterion closes the concrete longitudinal TT decomposition
target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramKernelGeneratorMapZeroData
    (D : PeriodicTTGramKernelGeneratorMapZeroData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramKernelCriterionData
    (PeriodicTTGramKernelCriterionData5.ofKernelGeneratorMapZeroData D)

/-- The finite Gram range criterion is enough to close the concrete longitudinal
TT decomposition target. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramRangeCriterionData
    (D : PeriodicTTGramRangeCriterionData5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramKernelCriterionData
    (PeriodicTTGramKernelCriterionData5.ofRangeCriterionData D)

/-- The concrete longitudinal TT decomposition target is closed by the proved
finite Gram range theorem. -/
theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_provedGramRangeCriterion :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5
      (PeriodicLongitudinalGaugeIdx5 → ℝ) periodicLongitudinalGaugeMap5 :=
  periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_of_gramRangeCriterionData
    periodicTTGramRangeCriterionData5_proved

/-! ## TT Hessian-to-Lichnerowicz matching surface -/

/-- Bilinear form induced by an edge-space operator and the finite periodic-edge
inner product. -/
def periodicTTOperatorBilinear5
    (op : PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5)
    (ε η : PeriodicEdgePerturbation5) : ℝ :=
  periodicEdgeInnerProduct5 ε (op η)

/-- Finite edge-kernel representation of an operator on periodic edge
perturbations.  This is the concrete matrix surface where the Regge TT Hessian
stencil and the lattice Lichnerowicz stencil should be compared. -/
abbrev PeriodicEdgeOperatorKernel5 :=
  PeriodicEdge5 → PeriodicEdge5 → ℝ

/-- Encoded finite-triangulation version of an edge-kernel matrix.  This is the
native `Fin K.nE` index surface for kernels extracted from the encoded
Freudenthal triangulation. -/
abbrev EncodedEdgeOperatorKernel5 :=
  Fin PeriodicTorus5.K.nE → Fin PeriodicTorus5.K.nE → ℝ

/-- Pull an encoded `Fin K.nE` edge kernel back to typed periodic-edge indices. -/
def encodedToPeriodicEdgeKernel5
    (kernel : EncodedEdgeOperatorKernel5) : PeriodicEdgeOperatorKernel5 :=
  fun e f => kernel (PeriodicTorus5.edgeEquiv.symm e) (PeriodicTorus5.edgeEquiv.symm f)

theorem encodedToPeriodicEdgeKernel5_apply
    (kernel : EncodedEdgeOperatorKernel5) (e f : PeriodicEdge5) :
    encodedToPeriodicEdgeKernel5 kernel e f =
      kernel (PeriodicTorus5.edgeEquiv.symm e) (PeriodicTorus5.edgeEquiv.symm f) :=
  rfl

/-- Difference kernel on the encoded finite edge-index surface. -/
def encodedEdgeKernelResidual5
    (reggeKernel lichnerowiczKernel : EncodedEdgeOperatorKernel5) :
    EncodedEdgeOperatorKernel5 :=
  fun e f => reggeKernel e f - lichnerowiczKernel e f

theorem encodedEdgeKernelResidual5_apply
    (reggeKernel lichnerowiczKernel : EncodedEdgeOperatorKernel5)
    (e f : Fin PeriodicTorus5.K.nE) :
    encodedEdgeKernelResidual5 reggeKernel lichnerowiczKernel e f =
      reggeKernel e f - lichnerowiczKernel e f :=
  rfl

/-- The origin vertex of the concrete `5 × 5 × 5` periodic torus. -/
def periodicOriginVertex5 : PeriodicVertex5 :=
  (0, 0, 0)

/-- Coordinate subtraction on the concrete `N = 5` torus. -/
def periodicSubFin5 (base v : Fin 5) : Fin 5 :=
  ⟨(v.1 + (5 - base.1)) % 5, by omega⟩

/-- Vertex coordinates of `v` in the frame whose origin is `base`. -/
def periodicRelativeVertex5 (base v : PeriodicVertex5) : PeriodicVertex5 :=
  (periodicSubFin5 base.1 v.1,
   periodicSubFin5 base.2.1 v.2.1,
   periodicSubFin5 base.2.2 v.2.2)

theorem periodicRelativeVertex5_origin_eq_self (v : PeriodicVertex5) :
    periodicRelativeVertex5 periodicOriginVertex5 v = v := by
  rcases v with ⟨x, y, z⟩
  ext <;> simp [periodicRelativeVertex5, periodicSubFin5, periodicOriginVertex5]

/-- Translating a relative-frame vertex back by its frame origin recovers the
original global vertex. -/
theorem periodicTranslateVertex5_relative_eq_self
    (base v : PeriodicVertex5) :
    periodicTranslateVertex5 base (periodicRelativeVertex5 base v) = v := by
  rcases base with ⟨bx, byz⟩
  rcases byz with ⟨byc, bz⟩
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  ext <;> simp [periodicTranslateVertex5, periodicRelativeVertex5,
    periodicAddFin5, periodicSubFin5] <;> omega

/-- Re-basing a translated vertex at the same origin recovers the original
relative vertex. -/
theorem periodicRelativeVertex5_translate_eq_self
    (base v : PeriodicVertex5) :
    periodicRelativeVertex5 base (periodicTranslateVertex5 base v) = v := by
  rcases base with ⟨bx, byz⟩
  rcases byz with ⟨byc, bz⟩
  rcases v with ⟨x, yz⟩
  rcases yz with ⟨y, z⟩
  ext <;> simp [periodicTranslateVertex5, periodicRelativeVertex5,
    periodicAddFin5, periodicSubFin5] <;> omega

/-- Translation by a fixed periodic vertex is injective on the concrete torus. -/
theorem periodicTranslateVertex5_injective
    (base : PeriodicVertex5) :
    Function.Injective (periodicTranslateVertex5 base) := by
  intro v w h
  have hrel := congrArg (periodicRelativeVertex5 base) h
  simpa [periodicRelativeVertex5_translate_eq_self] using hrel

/-- The origin-row representative for a periodic edge displacement. -/
def periodicOriginEdgeOfDisp5 (disp : Fin 7) : PeriodicEdge5 :=
  { base := periodicOriginVertex5, disp := disp }

/-- Column edge written in the coordinate frame of a row edge. -/
def periodicRelativeColumnOfRow5
    (row col : PeriodicEdge5) : PeriodicEdge5 :=
  { base := periodicRelativeVertex5 row.base col.base, disp := col.disp }

theorem periodicRelativeColumnOfOriginDisp5
    (rowDisp colDisp : Fin 7) (colBase : PeriodicVertex5) :
    periodicRelativeColumnOfRow5
        (periodicOriginEdgeOfDisp5 rowDisp)
        ({ base := colBase, disp := colDisp } : PeriodicEdge5) =
      ({ base := colBase, disp := colDisp } : PeriodicEdge5) := by
  simp [periodicRelativeColumnOfRow5, periodicOriginEdgeOfDisp5,
    periodicRelativeVertex5_origin_eq_self]

/-- Endpoints of a relative-frame column are the relative-frame endpoints of the
global column. -/
theorem periodicRelativeColumnOfRow5_endpoints
    (row col : PeriodicEdge5) :
    (periodicRelativeColumnOfRow5 row col).endpoints =
      (periodicRelativeVertex5 row.base col.endpoints.1,
       periodicRelativeVertex5 row.base col.endpoints.2) := by
  rcases row with ⟨rowBase, rowDisp⟩
  rcases col with ⟨colBase, colDisp⟩
  rcases rowBase with ⟨rx, ryz⟩
  rcases ryz with ⟨ry, rz⟩
  rcases colBase with ⟨cx, cyz⟩
  rcases cyz with ⟨cy, cz⟩
  fin_cases colDisp <;>
    ext <;>
    simp [periodicRelativeColumnOfRow5, PeriodicEdge.endpoints,
      periodicRelativeVertex5, periodicSubFin5, addBits, dispBits, addBit, bit] <;>
    omega

/-- Translating the endpoints of a relative-frame column back by the row base
recovers the endpoints of the original global column. -/
theorem periodicTranslateVertex5_relativeColumn_endpoints
    (row col : PeriodicEdge5) :
    (periodicTranslateVertex5 row.base
        (periodicRelativeColumnOfRow5 row col).endpoints.1,
      periodicTranslateVertex5 row.base
        (periodicRelativeColumnOfRow5 row col).endpoints.2) =
      col.endpoints := by
  rw [periodicRelativeColumnOfRow5_endpoints]
  simp [periodicTranslateVertex5_relative_eq_self]

/-- First endpoint equality in a row-relative frame is equivalent to translated
global endpoint equality. -/
theorem periodicRelativeColumnOfRow5_endpoint_fst_eq_iff
    (row col : PeriodicEdge5) (v : PeriodicVertex5) :
    (periodicRelativeColumnOfRow5 row col).endpoints.1 = v ↔
      col.endpoints.1 = periodicTranslateVertex5 row.base v := by
  have hends := periodicTranslateVertex5_relativeColumn_endpoints row col
  have hfst :
      periodicTranslateVertex5 row.base
          (periodicRelativeColumnOfRow5 row col).endpoints.1 =
        col.endpoints.1 := congrArg Prod.fst hends
  constructor
  · intro h
    rw [← hfst, h]
  · intro h
    exact periodicTranslateVertex5_injective row.base (hfst.trans h)

/-- Second endpoint equality in a row-relative frame is equivalent to translated
global endpoint equality. -/
theorem periodicRelativeColumnOfRow5_endpoint_snd_eq_iff
    (row col : PeriodicEdge5) (v : PeriodicVertex5) :
    (periodicRelativeColumnOfRow5 row col).endpoints.2 = v ↔
      col.endpoints.2 = periodicTranslateVertex5 row.base v := by
  have hends := periodicTranslateVertex5_relativeColumn_endpoints row col
  have hsnd :
      periodicTranslateVertex5 row.base
          (periodicRelativeColumnOfRow5 row col).endpoints.2 =
        col.endpoints.2 := congrArg Prod.snd hends
  constructor
  · intro h
    rw [← hsnd, h]
  · intro h
    exact periodicTranslateVertex5_injective row.base (hsnd.trans h)

/-- Encoded first-endpoint equality in a row-relative frame is equivalent to
encoded shifted first-endpoint equality in the global frame. -/
theorem periodicRelativeColumnOfRow5_encoded_endpoint_fst_eq_iff
    (row col : PeriodicEdge5) (v : Fin PeriodicTorus5.K.nV) :
    periodicVertexEquiv5.symm
        (periodicRelativeColumnOfRow5 row col).endpoints.1 = v ↔
      periodicVertexEquiv5.symm col.endpoints.1 =
        periodicTranslateEncodedVertexIdx5 row.base v := by
  constructor
  · intro h
    apply periodicVertexEquiv5.injective
    simpa [periodicTranslateEncodedVertexIdx5] using
      (periodicRelativeColumnOfRow5_endpoint_fst_eq_iff row col
        (periodicVertexEquiv5 v)).1 (by
          simpa using congrArg periodicVertexEquiv5 h)
  · intro h
    have hglobal :
        col.endpoints.1 =
          periodicTranslateVertex5 row.base (periodicVertexEquiv5 v) := by
      simpa [periodicTranslateEncodedVertexIdx5] using
        congrArg periodicVertexEquiv5 h
    have hrel :=
      (periodicRelativeColumnOfRow5_endpoint_fst_eq_iff row col
        (periodicVertexEquiv5 v)).2 hglobal
    simpa using congrArg periodicVertexEquiv5.symm hrel

/-- Encoded second-endpoint equality in a row-relative frame is equivalent to
encoded shifted second-endpoint equality in the global frame. -/
theorem periodicRelativeColumnOfRow5_encoded_endpoint_snd_eq_iff
    (row col : PeriodicEdge5) (v : Fin PeriodicTorus5.K.nV) :
    periodicVertexEquiv5.symm
        (periodicRelativeColumnOfRow5 row col).endpoints.2 = v ↔
      periodicVertexEquiv5.symm col.endpoints.2 =
        periodicTranslateEncodedVertexIdx5 row.base v := by
  constructor
  · intro h
    apply periodicVertexEquiv5.injective
    simpa [periodicTranslateEncodedVertexIdx5] using
      (periodicRelativeColumnOfRow5_endpoint_snd_eq_iff row col
        (periodicVertexEquiv5 v)).1 (by
          simpa using congrArg periodicVertexEquiv5 h)
  · intro h
    have hglobal :
        col.endpoints.2 =
          periodicTranslateVertex5 row.base (periodicVertexEquiv5 v) := by
      simpa [periodicTranslateEncodedVertexIdx5] using
        congrArg periodicVertexEquiv5 h
    have hrel :=
      (periodicRelativeColumnOfRow5_endpoint_snd_eq_iff row col
        (periodicVertexEquiv5 v)).2 hglobal
    simpa using congrArg periodicVertexEquiv5.symm hrel

/-- A row-frame translate of one conformal generator column is exactly the
globally shifted conformal generator column. -/
theorem periodicConformalGenerator5_relativeColumn_eq_shift
    (row col : PeriodicEdge5) (v : Fin PeriodicTorus5.K.nV) :
    periodicConformalGenerator5 v
        (periodicRelativeColumnOfRow5 row col) =
      periodicConformalGenerator5
        (periodicTranslateEncodedVertexIdx5 row.base v) col := by
  rw [periodicConformalGenerator5_apply_endpoint,
    periodicConformalGenerator5_apply_endpoint]
  simp [periodicRelativeColumnOfRow5_encoded_endpoint_fst_eq_iff,
    periodicRelativeColumnOfRow5_encoded_endpoint_snd_eq_iff]

/-- A row-frame translate of one longitudinal gauge generator column is exactly
the globally shifted longitudinal gauge generator column. -/
theorem periodicLongitudinalGaugeGenerator5_relativeColumn_eq_shift
    (row col : PeriodicEdge5) (idx : PeriodicLongitudinalGaugeIdx5) :
    periodicLongitudinalGaugeGenerator5 idx
        (periodicRelativeColumnOfRow5 row col) =
      periodicLongitudinalGaugeGenerator5
        (periodicTranslateLongitudinalGaugeIdx5 row.base idx) col := by
  rcases idx with ⟨idxVertex, idxComponent⟩
  have hdisp : (periodicRelativeColumnOfRow5 row col).disp = col.disp := rfl
  simp [periodicLongitudinalGaugeGenerator5,
    periodicTranslateLongitudinalGaugeIdx5,
    hdisp,
    periodicRelativeColumnOfRow5_endpoint_fst_eq_iff,
    periodicRelativeColumnOfRow5_endpoint_snd_eq_iff]

/-- A row-frame translate of any combined normal-equation generator column is
exactly the globally shifted combined generator column. -/
theorem periodicTTNormalEquationGenerator5_relativeColumn_eq_shift
    (row col : PeriodicEdge5) (idx : PeriodicTTNormalEquationIdx5) :
    periodicTTNormalEquationGenerator5 idx
        (periodicRelativeColumnOfRow5 row col) =
      periodicTTNormalEquationGenerator5
        (periodicTranslateTTNormalEquationIdx5 row.base idx) col := by
  cases idx with
  | inl v =>
      exact periodicConformalGenerator5_relativeColumn_eq_shift row col v
  | inr i =>
      exact periodicLongitudinalGaugeGenerator5_relativeColumn_eq_shift row col i

/-- Encoded vertex-index translation by a row base, packaged as an equivalence. -/
noncomputable def periodicTranslateEncodedVertexIdxEquiv5
    (base : PeriodicVertex5) :
    Fin PeriodicTorus5.K.nV ≃ Fin PeriodicTorus5.K.nV where
  toFun := periodicTranslateEncodedVertexIdx5 base
  invFun := fun v =>
    periodicVertexEquiv5.symm
      (periodicRelativeVertex5 base (periodicVertexEquiv5 v))
  left_inv := by
    intro v
    apply periodicVertexEquiv5.injective
    simp [periodicTranslateEncodedVertexIdx5,
      periodicRelativeVertex5_translate_eq_self]
  right_inv := by
    intro v
    apply periodicVertexEquiv5.injective
    simp [periodicTranslateEncodedVertexIdx5,
      periodicTranslateVertex5_relative_eq_self]

/-- Longitudinal gauge-index translation by a row base, packaged as an equivalence. -/
def periodicTranslateLongitudinalGaugeIdxEquiv5
    (base : PeriodicVertex5) :
    PeriodicLongitudinalGaugeIdx5 ≃ PeriodicLongitudinalGaugeIdx5 where
  toFun := periodicTranslateLongitudinalGaugeIdx5 base
  invFun := fun idx => (periodicRelativeVertex5 base idx.1, idx.2)
  left_inv := by
    intro idx
    rcases idx with ⟨v, j⟩
    simp [periodicTranslateLongitudinalGaugeIdx5,
      periodicRelativeVertex5_translate_eq_self]
  right_inv := by
    intro idx
    rcases idx with ⟨v, j⟩
    simp [periodicTranslateLongitudinalGaugeIdx5,
      periodicTranslateVertex5_relative_eq_self]

/-- Combined normal-equation index translation by a row base, packaged as an
equivalence. -/
noncomputable def periodicTranslateTTNormalEquationIdxEquiv5
    (base : PeriodicVertex5) :
    PeriodicTTNormalEquationIdx5 ≃ PeriodicTTNormalEquationIdx5 where
  toFun := periodicTranslateTTNormalEquationIdx5 base
  invFun
    | Sum.inl v => Sum.inl ((periodicTranslateEncodedVertexIdxEquiv5 base).symm v)
    | Sum.inr i => Sum.inr ((periodicTranslateLongitudinalGaugeIdxEquiv5 base).symm i)
  left_inv := by
    intro idx
    cases idx with
    | inl v =>
        simp only [periodicTranslateTTNormalEquationIdx5]
        exact congrArg Sum.inl
          ((periodicTranslateEncodedVertexIdxEquiv5 base).left_inv v)
    | inr i =>
        simp only [periodicTranslateTTNormalEquationIdx5]
        exact congrArg Sum.inr
          ((periodicTranslateLongitudinalGaugeIdxEquiv5 base).left_inv i)
  right_inv := by
    intro idx
    cases idx with
    | inl v =>
        simp only [periodicTranslateTTNormalEquationIdx5]
        exact congrArg Sum.inl
          ((periodicTranslateEncodedVertexIdxEquiv5 base).right_inv v)
    | inr i =>
        simp only [periodicTranslateTTNormalEquationIdx5]
        exact congrArg Sum.inr
          ((periodicTranslateLongitudinalGaugeIdxEquiv5 base).right_inv i)

/-- Combined generator map viewed in the coordinate frame of a row edge. -/
def periodicRelativeTTNormalEquationGeneratorMap5
    (row : PeriodicEdge5) (coeff : PeriodicTTNormalEquationIdx5 → ℝ) :
    PeriodicEdgePerturbation5 :=
  fun col => periodicTTNormalEquationGeneratorMap5 coeff
    (periodicRelativeColumnOfRow5 row col)

/-- Relative-frame combined generator maps are global generator maps with the
coefficient vector reindexed by the row-base translation equivalence. -/
theorem periodicRelativeTTNormalEquationGeneratorMap5_eq_shiftedMap
    (row : PeriodicEdge5) (coeff : PeriodicTTNormalEquationIdx5 → ℝ)
    (col : PeriodicEdge5) :
    periodicRelativeTTNormalEquationGeneratorMap5 row coeff col =
      periodicTTNormalEquationGeneratorMap5
        (fun idx => coeff ((periodicTranslateTTNormalEquationIdxEquiv5 row.base).symm idx))
        col := by
  classical
  let σ := periodicTranslateTTNormalEquationIdxEquiv5 row.base
  unfold periodicRelativeTTNormalEquationGeneratorMap5
    periodicTTNormalEquationGeneratorMap5 periodicGaugeGeneratorMap5
  calc
    (∑ idx : PeriodicTTNormalEquationIdx5,
        coeff idx *
          periodicTTNormalEquationGenerator5 idx
            (periodicRelativeColumnOfRow5 row col)) =
      ∑ idx : PeriodicTTNormalEquationIdx5,
        coeff idx *
          periodicTTNormalEquationGenerator5 (σ idx) col := by
        refine Finset.sum_congr rfl ?_
        intro idx _
        rw [periodicTTNormalEquationGenerator5_relativeColumn_eq_shift]
        rfl
    _ =
      ∑ idx : PeriodicTTNormalEquationIdx5,
        coeff (σ.symm idx) *
          periodicTTNormalEquationGenerator5 idx col := by
        exact Fintype.sum_equiv σ
          (fun idx : PeriodicTTNormalEquationIdx5 =>
            coeff idx * periodicTTNormalEquationGenerator5 (σ idx) col)
          (fun idx : PeriodicTTNormalEquationIdx5 =>
            coeff (σ.symm idx) * periodicTTNormalEquationGenerator5 idx col)
          (fun idx => by simp [σ])

/-- Missing shifted-generator lemma for the relative-frame route: every TT
perturbation is orthogonal to every row-frame translate of the combined
conformal/longitudinal generator map. -/
def PeriodicRelativeTTGeneratorOrthogonalOnTT5 : Prop :=
  ∀ ε,
    PeriodicLongitudinalTTSubspace5 ε →
      ∀ (row : PeriodicEdge5) (coeff : PeriodicTTNormalEquationIdx5 → ℝ),
        periodicEdgeInnerProduct5 ε
          (periodicRelativeTTNormalEquationGeneratorMap5 row coeff) = 0

/-- Closure target behind shifted-generator orthogonality: every row-frame
translate of a combined normal-equation generator must split back into the
fixed conformal and longitudinal-gauge images. -/
def PeriodicRelativeTTGeneratorClosure5 : Prop :=
  ∀ (row : PeriodicEdge5) (coeff : PeriodicTTNormalEquationIdx5 → ℝ),
    ∃ (conformalCoeff : Fin PeriodicTorus5.K.nV → ℝ)
      (gaugeCoeff : PeriodicLongitudinalGaugeIdx5 → ℝ),
      ∀ col,
        periodicRelativeTTNormalEquationGeneratorMap5 row coeff col =
          periodicConformalGeneratorMap5 conformalCoeff col +
            periodicLongitudinalGaugeMap5 gaugeCoeff col

/-- The row-frame translated combined generator space is exactly closed inside
the fixed conformal plus longitudinal-gauge image. -/
theorem periodicRelativeTTGeneratorClosure5_holds :
    PeriodicRelativeTTGeneratorClosure5 := by
  classical
  intro row coeff
  let shiftedCoeff : PeriodicTTNormalEquationIdx5 → ℝ :=
    fun idx => coeff ((periodicTranslateTTNormalEquationIdxEquiv5 row.base).symm idx)
  refine ⟨
    periodicTTNormalEquationConformalCoeff5 shiftedCoeff,
    periodicTTNormalEquationGaugeCoeff5 shiftedCoeff,
    ?_⟩
  intro col
  rw [periodicRelativeTTNormalEquationGeneratorMap5_eq_shiftedMap]
  exact periodicTTNormalEquationGeneratorMap5_eq_split shiftedCoeff col

/-- Closure of row-frame generator translates into the fixed conformal/gauge
images proves the shifted-generator orthogonality lemma. -/
theorem PeriodicRelativeTTGeneratorOrthogonalOnTT5.ofClosure
    (hclosure : PeriodicRelativeTTGeneratorClosure5) :
    PeriodicRelativeTTGeneratorOrthogonalOnTT5 := by
  intro ε hε row coeff
  rcases hclosure row coeff with ⟨conformalCoeff, gaugeCoeff, hsplit⟩
  have hfun :
      periodicRelativeTTNormalEquationGeneratorMap5 row coeff =
        fun col =>
          periodicConformalGeneratorMap5 conformalCoeff col +
            periodicLongitudinalGaugeMap5 gaugeCoeff col := by
    funext col
    exact hsplit col
  have hc :
      periodicEdgeInnerProduct5 ε
        (periodicConformalGeneratorMap5 conformalCoeff) = 0 :=
    hε.1 (periodicConformalGeneratorMap5 conformalCoeff)
      (periodicConformalGeneratorMap5_mem conformalCoeff)
  have hg :
      periodicEdgeInnerProduct5 ε
        (periodicLongitudinalGaugeMap5 gaugeCoeff) = 0 :=
    hε.2 (periodicLongitudinalGaugeMap5 gaugeCoeff) ⟨gaugeCoeff, rfl⟩
  rw [hfun, periodicEdgeInnerProduct5_add_right, hc, hg, add_zero]

/-- Encoded edge index for the origin-row representative of a displacement. -/
def encodedOriginEdgeOfDisp5 (disp : Fin 7) : Fin PeriodicTorus5.K.nE :=
  PeriodicTorus5.edgeEquiv.symm (periodicOriginEdgeOfDisp5 disp)

theorem encodedOriginEdgeOfDisp5_equiv
    (disp : Fin 7) :
    PeriodicTorus5.edgeEquiv (encodedOriginEdgeOfDisp5 disp) =
      periodicOriginEdgeOfDisp5 disp := by
  simp [encodedOriginEdgeOfDisp5]

/-- Apply a finite edge-kernel operator to an edge perturbation. -/
def periodicEdgeKernelOperator5
    (kernel : PeriodicEdgeOperatorKernel5)
    (ε : PeriodicEdgePerturbation5) : PeriodicEdgePerturbation5 :=
  fun e => ∑ f : PeriodicEdge5, kernel e f * ε f

/-- Row of a finite edge-kernel operator as an edge perturbation. -/
def periodicEdgeKernelRowVector5
    (kernel : PeriodicEdgeOperatorKernel5)
    (e : PeriodicEdge5) : PeriodicEdgePerturbation5 :=
  fun f => kernel e f

/-- Kernel-operator evaluation is pairing against the corresponding row vector,
up to the symmetry of real multiplication. -/
theorem periodicEdgeKernelOperator5_eq_inner_row
    (kernel : PeriodicEdgeOperatorKernel5)
    (ε : PeriodicEdgePerturbation5)
    (e : PeriodicEdge5) :
    periodicEdgeKernelOperator5 kernel ε e =
      periodicEdgeInnerProduct5 ε (periodicEdgeKernelRowVector5 kernel e) := by
  unfold periodicEdgeKernelOperator5 periodicEdgeInnerProduct5 periodicEdgeKernelRowVector5
  refine Finset.sum_congr rfl ?_
  intro f _
  ring

/-- Rowwise agreement of edge-kernel operators on a TT perturbation gives
pointwise agreement of the resulting edge perturbations. -/
theorem periodicEdgeKernelOperator5_eq_of_row_eq
    (reggeKernel lichnerowiczKernel : PeriodicEdgeOperatorKernel5)
    (ε : PeriodicEdgePerturbation5)
    (hrow :
      ∀ e : PeriodicEdge5,
        periodicEdgeKernelOperator5 reggeKernel ε e =
          periodicEdgeKernelOperator5 lichnerowiczKernel ε e) :
    periodicEdgeKernelOperator5 reggeKernel ε =
      periodicEdgeKernelOperator5 lichnerowiczKernel ε := by
  funext e
  exact hrow e

/-- Entrywise equality of two finite edge kernels gives equality of their
operators on every edge perturbation. -/
theorem periodicEdgeKernelOperator5_eq_of_kernel_eq
    (reggeKernel lichnerowiczKernel : PeriodicEdgeOperatorKernel5)
    (hkernel : ∀ e f : PeriodicEdge5, reggeKernel e f = lichnerowiczKernel e f)
    (ε : PeriodicEdgePerturbation5) :
    periodicEdgeKernelOperator5 reggeKernel ε =
      periodicEdgeKernelOperator5 lichnerowiczKernel ε := by
  apply periodicEdgeKernelOperator5_eq_of_row_eq
  intro e
  unfold periodicEdgeKernelOperator5
  refine Finset.sum_congr rfl ?_
  intro f _
  rw [hkernel e f]

/-- Difference kernel between the Regge TT Hessian stencil and the lattice
Lichnerowicz stencil. -/
def periodicEdgeKernelResidual5
    (reggeKernel lichnerowiczKernel : PeriodicEdgeOperatorKernel5) :
    PeriodicEdgeOperatorKernel5 :=
  fun e f => reggeKernel e f - lichnerowiczKernel e f

/-- Applying the residual kernel is the difference of the two kernel operators. -/
theorem periodicEdgeKernelOperator5_residual_eq_sub
    (reggeKernel lichnerowiczKernel : PeriodicEdgeOperatorKernel5)
    (ε : PeriodicEdgePerturbation5)
    (e : PeriodicEdge5) :
    periodicEdgeKernelOperator5
      (periodicEdgeKernelResidual5 reggeKernel lichnerowiczKernel) ε e =
      periodicEdgeKernelOperator5 reggeKernel ε e -
        periodicEdgeKernelOperator5 lichnerowiczKernel ε e := by
  unfold periodicEdgeKernelOperator5 periodicEdgeKernelResidual5
  calc
    (∑ f : PeriodicEdge5, (reggeKernel e f - lichnerowiczKernel e f) * ε f)
        =
        ∑ f : PeriodicEdge5,
          (reggeKernel e f * ε f - lichnerowiczKernel e f * ε f) := by
          refine Finset.sum_congr rfl ?_
          intro f _
          ring
    _ =
        (∑ f : PeriodicEdge5, reggeKernel e f * ε f) -
          ∑ f : PeriodicEdge5, lichnerowiczKernel e f * ε f := by
          rw [Finset.sum_sub_distrib]

/-- The exact forward Track 1.D Hessian/Lichnerowicz target at `N = 5`: on TT
edge perturbations, the Regge Hessian operator agrees with the lattice
Lichnerowicz operator. -/
def PeriodicTTHessianMatchesLichnerowiczAtN5
    (reggeHessianTT latticeLichnerowiczTT :
      PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5) : Prop :=
  ∀ ε,
    PeriodicLongitudinalTTSubspace5 ε →
      reggeHessianTT ε = latticeLichnerowiczTT ε

/-- Data object for the TT Hessian-to-Lichnerowicz operator match.  The actual
analytic work is to instantiate the two operators from the Regge Hessian and the
discrete spin-2 Lichnerowicz stencil, then prove `matches_on_tt`. -/
structure PeriodicTTHessianLichnerowiczMatchData5 where
  reggeHessianTT :
    PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  latticeLichnerowiczTT :
    PeriodicEdgePerturbation5 → PeriodicEdgePerturbation5
  matches_on_tt :
    PeriodicTTHessianMatchesLichnerowiczAtN5
      reggeHessianTT latticeLichnerowiczTT

/-- Rowwise kernel data for proving the TT Hessian-to-Lichnerowicz operator
match.  The intended physical closure is to instantiate `reggeHessianKernel`
from the Regge second-variation edge Hessian and `latticeLichnerowiczKernel`
from the spin-2 lattice stencil, then prove `kernel_rows_match_on_tt`. -/
structure PeriodicTTHessianLichnerowiczKernelRowData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  kernel_rows_match_on_tt :
    ∀ ε,
      PeriodicLongitudinalTTSubspace5 ε →
        ∀ e : PeriodicEdge5,
          periodicEdgeKernelOperator5 reggeHessianKernel ε e =
            periodicEdgeKernelOperator5 latticeLichnerowiczKernel ε e

/-- Entrywise kernel data is a stronger, stencil-level route to the same TT
Hessian-to-Lichnerowicz operator match. -/
structure PeriodicTTHessianLichnerowiczKernelEntryData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  kernel_entries_match :
    ∀ e f : PeriodicEdge5,
      reggeHessianKernel e f = latticeLichnerowiczKernel e f

/-- Residual-kernel vanishing on TT perturbations is the most compact finite
calculation target for the TT Hessian-to-Lichnerowicz comparison. -/
structure PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  residual_zero_on_tt :
    ∀ ε,
      PeriodicLongitudinalTTSubspace5 ε →
        periodicEdgeKernelOperator5
          (periodicEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel)
          ε = fun _ => 0

/-- Row-span data for the residual kernel: every residual row belongs to the
combined conformal plus longitudinal generator span.  This is the sharp finite
stencil target for the TT Hessian/Lichnerowicz comparison. -/
structure PeriodicTTHessianLichnerowiczResidualRowSpanData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  residual_row_mem_generator_span :
    ∀ e : PeriodicEdge5,
      ∃ coeff : PeriodicTTNormalEquationIdx5 → ℝ,
        periodicEdgeKernelRowVector5
          (periodicEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel) e =
          periodicTTNormalEquationGeneratorMap5 coeff

/-- Explicit coefficient form of the residual-row span target.  This is the
finite table the remaining TT stencil calculation should produce: for each
edge-row, a combined conformal/longitudinal coefficient vector whose generator
map is exactly the residual row. -/
structure PeriodicTTHessianLichnerowiczResidualRowCoeffData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  residualRowCoeff :
    PeriodicEdge5 → PeriodicTTNormalEquationIdx5 → ℝ
  residual_row_eq_generatorMap :
    ∀ e : PeriodicEdge5,
      periodicEdgeKernelRowVector5
        (periodicEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel) e =
        periodicTTNormalEquationGeneratorMap5 (residualRowCoeff e)

/-- Entrywise version of the explicit residual-row coefficient target.  This is
the certificate-friendly scalar form: every residual kernel entry equals the
corresponding entry of the row's generator-map reconstruction. -/
structure PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  residualRowCoeff :
    PeriodicEdge5 → PeriodicTTNormalEquationIdx5 → ℝ
  residual_entry_eq_generatorMap :
    ∀ e f : PeriodicEdge5,
      periodicEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5 (residualRowCoeff e) f

/-- Raw scalar formula form of the residual-row coefficient target.  This is the
unwrapped finite identity: Regge kernel entry minus Lichnerowicz kernel entry
equals the generator-map reconstruction entry. -/
structure PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 where
  reggeHessianKernel : PeriodicEdgeOperatorKernel5
  latticeLichnerowiczKernel : PeriodicEdgeOperatorKernel5
  residualRowCoeff :
    PeriodicEdge5 → PeriodicTTNormalEquationIdx5 → ℝ
  residual_entry_formula :
    ∀ e f : PeriodicEdge5,
      reggeHessianKernel e f - latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5 (residualRowCoeff e) f

/-- Encoded finite-index form of the raw scalar TT residual formula.  This is
the certificate surface for kernels produced over the encoded `Fin K.nE` edge
indexing of the canonical `N = 5` periodic Freudenthal torus. -/
structure EncodedTTHessianLichnerowiczResidualEntryFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualRowCoeff :
    PeriodicEdge5 → PeriodicTTNormalEquationIdx5 → ℝ
  encoded_residual_entry_formula :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      reggeHessianKernel e f - latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5
          (residualRowCoeff (PeriodicTorus5.edgeEquiv e))
          (PeriodicTorus5.edgeEquiv f)

/-- Encoded residual-kernel certificate form.  This lets the finite calculation
emit the already-subtracted residual matrix, prove it is `Regge - Lichnerowicz`,
and then compare that residual directly to the generator-map reconstruction. -/
structure EncodedTTHessianLichnerowiczResidualKernelFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualKernel : EncodedEdgeOperatorKernel5
  residualRowCoeff :
    PeriodicEdge5 → PeriodicTTNormalEquationIdx5 → ℝ
  residualKernel_eq_sub :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f
  residualKernel_entry_formula :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        periodicTTNormalEquationGeneratorMap5
          (residualRowCoeff (PeriodicTorus5.edgeEquiv e))
          (PeriodicTorus5.edgeEquiv f)

/-- Displacement-row form of the encoded residual-kernel certificate.  Translation
normalizes every encoded row to the origin edge with the same displacement, so
the finite table only has seven row families. -/
structure EncodedTTHessianLichnerowiczResidualDispRowFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualKernel : EncodedEdgeOperatorKernel5
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  residualKernel_eq_sub :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f
  residualKernel_row_translation :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        residualKernel
          (encodedOriginEdgeOfDisp5 (PeriodicTorus5.edgeEquiv e).disp) f
  residual_origin_row_formula :
    ∀ (disp : Fin 7) (f : Fin PeriodicTorus5.K.nE),
      residualKernel (encodedOriginEdgeOfDisp5 disp) f =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff disp)
          (PeriodicTorus5.edgeEquiv f)

/-- Seven-row table form of the encoded residual certificate.  The generator can
emit only the origin residual rows, then separately prove that every matrix row
translates to the appropriate row of this table. -/
structure EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualKernel : EncodedEdgeOperatorKernel5
  residualOriginRow :
    Fin 7 → Fin PeriodicTorus5.K.nE → ℝ
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  residualKernel_eq_sub :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f
  residualOriginRow_eq_origin :
    ∀ (disp : Fin 7) (f : Fin PeriodicTorus5.K.nE),
      residualOriginRow disp f =
        residualKernel (encodedOriginEdgeOfDisp5 disp) f
  residualKernel_row_translation :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        residualOriginRow (PeriodicTorus5.edgeEquiv e).disp f
  residualOriginRow_entry_formula :
    ∀ (disp : Fin 7) (f : Fin PeriodicTorus5.K.nE),
      residualOriginRow disp f =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff disp)
          (PeriodicTorus5.edgeEquiv f)

/-- Typed-column table form of the seven origin-row residual certificate.  This
is the generator-facing surface: each table entry is indexed by the origin-row
displacement, the column base vertex, and the column displacement. -/
structure EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualKernel : EncodedEdgeOperatorKernel5
  residualOriginColumn :
    Fin 7 → PeriodicVertex5 → Fin 7 → ℝ
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  residualKernel_eq_sub :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f
  residualOriginColumn_eq_origin :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      residualOriginColumn rowDisp colBase colDisp =
        residualKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5))
  residualKernel_row_translation :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      residualKernel e f =
        residualOriginColumn
          (PeriodicTorus5.edgeEquiv e).disp
          (PeriodicTorus5.edgeEquiv f).base
          (PeriodicTorus5.edgeEquiv f).disp
  residualOriginColumn_entry_formula :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      residualOriginColumn rowDisp colBase colDisp =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff rowDisp)
          ({ base := colBase, disp := colDisp } : PeriodicEdge5)

/-- Raw typed-column residual certificate.  This removes the explicit residual
matrix from the generator-facing input: the finite calculation supplies only the
origin-column residual table and a translation law for the encoded
`Regge - Lichnerowicz` residual. -/
structure EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualOriginColumn :
    Fin 7 → PeriodicVertex5 → Fin 7 → ℝ
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  residualOriginColumn_eq_sub :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      residualOriginColumn rowDisp colBase colDisp =
        reggeHessianKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5)) -
        latticeLichnerowiczKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5))
  encodedResidual_row_translation :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f =
        residualOriginColumn
          (PeriodicTorus5.edgeEquiv e).disp
          (PeriodicTorus5.edgeEquiv f).base
          (PeriodicTorus5.edgeEquiv f).disp
  residualOriginColumn_entry_formula :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      residualOriginColumn rowDisp colBase colDisp =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff rowDisp)
          ({ base := colBase, disp := colDisp } : PeriodicEdge5)

/-- Coefficient-only origin-column formula data for the TT
Hessian/Lichnerowicz residual.  This is the smallest generator-facing surface:
it stores the two kernels and the seven residual-generator coefficient rows,
then proves the origin-row scalar formulas and the translated residual formula
directly against the generator map. -/
structure EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  originColumn_entry_formula :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      reggeHessianKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5)) -
        latticeLichnerowiczKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5)) =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff rowDisp)
          ({ base := colBase, disp := colDisp } : PeriodicEdge5)
  encodedResidual_entry_formula :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff (PeriodicTorus5.edgeEquiv e).disp)
          (PeriodicTorus5.edgeEquiv f)

/-- Coefficient-only translated residual formula data for the TT
Hessian/Lichnerowicz residual.  This is a smaller certificate surface than
`EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5`: once the translated
residual formula is known, the origin-column scalar formula follows by
specializing the row to the origin edge. -/
structure EncodedTTHessianLichnerowiczCoeffTranslatedFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  encodedResidual_entry_formula :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff (PeriodicTorus5.edgeEquiv e).disp)
          (PeriodicTorus5.edgeEquiv f)

/-- Origin-column formula data for a relative-frame translated residual
certificate.  This records the part of the relative certificate that agrees with
the existing origin-row generator map, without asserting the absolute translated
formula for every row. -/
structure EncodedTTHessianLichnerowiczCoeffRelativeOriginColumnFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  originColumn_entry_formula :
    ∀ (rowDisp : Fin 7) (colBase : PeriodicVertex5) (colDisp : Fin 7),
      reggeHessianKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5)) -
        latticeLichnerowiczKernel
          (encodedOriginEdgeOfDisp5 rowDisp)
          (PeriodicTorus5.edgeEquiv.symm
            ({ base := colBase, disp := colDisp } : PeriodicEdge5)) =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff rowDisp)
          ({ base := colBase, disp := colDisp } : PeriodicEdge5)

/-- Relative-frame coefficient-only translated residual formula data.  Generated
physical stencils are translation-covariant after each row is re-based at its
own edge base.  This diagnostic surface records that fact separately from the
stronger absolute translated certificate above. -/
structure EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5 where
  reggeHessianKernel : EncodedEdgeOperatorKernel5
  latticeLichnerowiczKernel : EncodedEdgeOperatorKernel5
  residualDispCoeff :
    Fin 7 → PeriodicTTNormalEquationIdx5 → ℝ
  encodedResidual_relative_entry_formula :
    ∀ e f : Fin PeriodicTorus5.K.nE,
      encodedEdgeKernelResidual5 reggeHessianKernel latticeLichnerowiczKernel e f =
        periodicTTNormalEquationGeneratorMap5
          (residualDispCoeff (PeriodicTorus5.edgeEquiv e).disp)
          (periodicRelativeColumnOfRow5
            (PeriodicTorus5.edgeEquiv e)
            (PeriodicTorus5.edgeEquiv f))

/-- Relative-frame translated data plus the shifted-generator orthogonality
lemma is enough to prove the residual kernel vanishes on TT perturbations.
The separate orthogonality field is the exact mathematical gap left by the
Regge Schläfli candidate diagnostics. -/
structure EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5 where
  relativeData : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5
  relativeGeneratorOrthogonalOnTT : PeriodicRelativeTTGeneratorOrthogonalOnTT5

/-- Relative-frame translated data plus the sharper generator-closure bridge.
This is the preferred mathematical target: prove closure once, then
orthogonality follows from the existing TT definition. -/
structure EncodedTTHessianLichnerowiczCoeffRelativeTranslatedClosureData5 where
  relativeData : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5
  relativeGeneratorClosure : PeriodicRelativeTTGeneratorClosure5

/-- Generator closure supplies the orthogonality package required by the
conditional relative-frame TT-zero route. -/
def EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5.ofClosureData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedClosureData5) :
    EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5 where
  relativeData := D.relativeData
  relativeGeneratorOrthogonalOnTT :=
    PeriodicRelativeTTGeneratorOrthogonalOnTT5.ofClosure D.relativeGeneratorClosure

/-- The shifted-generator closure theorem is now proved, so a relative-frame
translated certificate alone supplies the TT-zero package. -/
def EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5.ofRelativeTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5) :
    EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5 where
  relativeData := D
  relativeGeneratorOrthogonalOnTT :=
    PeriodicRelativeTTGeneratorOrthogonalOnTT5.ofClosure
      periodicRelativeTTGeneratorClosure5_holds

/-- Rowwise kernel data supplies the TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofKernelRowData
    (D : PeriodicTTHessianLichnerowiczKernelRowData5) :
    PeriodicTTHessianLichnerowiczMatchData5 where
  reggeHessianTT := periodicEdgeKernelOperator5 D.reggeHessianKernel
  latticeLichnerowiczTT := periodicEdgeKernelOperator5 D.latticeLichnerowiczKernel
  matches_on_tt := by
    intro ε hε
    exact periodicEdgeKernelOperator5_eq_of_row_eq
      D.reggeHessianKernel D.latticeLichnerowiczKernel ε
      (D.kernel_rows_match_on_tt ε hε)

/-- Entrywise kernel data supplies rowwise kernel data. -/
def PeriodicTTHessianLichnerowiczKernelRowData5.ofEntryData
    (D : PeriodicTTHessianLichnerowiczKernelEntryData5) :
    PeriodicTTHessianLichnerowiczKernelRowData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  kernel_rows_match_on_tt := by
    intro ε _hε e
    have h :=
      periodicEdgeKernelOperator5_eq_of_kernel_eq
        D.reggeHessianKernel D.latticeLichnerowiczKernel
        D.kernel_entries_match ε
    exact congrFun h e

/-- Residual-kernel vanishing on TT perturbations supplies rowwise kernel
matching on TT perturbations. -/
def PeriodicTTHessianLichnerowiczKernelRowData5.ofResidualTTZeroData
    (D : PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5) :
    PeriodicTTHessianLichnerowiczKernelRowData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  kernel_rows_match_on_tt := by
    intro ε hε e
    have hzero := congrFun (D.residual_zero_on_tt ε hε) e
    rw [periodicEdgeKernelOperator5_residual_eq_sub] at hzero
    exact sub_eq_zero.mp hzero

/-- Residual-row generator-span data proves that the residual kernel annihilates
every TT perturbation. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofResidualRowSpanData
    (D : PeriodicTTHessianLichnerowiczResidualRowSpanData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residual_zero_on_tt := by
    intro ε hε
    funext e
    rcases D.residual_row_mem_generator_span e with ⟨coeff, hrow⟩
    rw [periodicEdgeKernelOperator5_eq_inner_row]
    rw [hrow]
    exact periodicLongitudinalTTSubspace5_inner_generatorMap_eq_zero ε hε coeff

/-- Explicit residual-row coefficients supply residual-row span data. -/
def PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofRowCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffData5) :
    PeriodicTTHessianLichnerowiczResidualRowSpanData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residual_row_mem_generator_span := by
    intro e
    exact ⟨D.residualRowCoeff e, D.residual_row_eq_generatorMap e⟩

/-- Entrywise residual-row coefficients supply row-coefficient data. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEntryData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualRowCoeff := D.residualRowCoeff
  residual_row_eq_generatorMap := by
    intro e
    funext f
    exact D.residual_entry_eq_generatorMap e f

/-- Raw scalar residual formulas supply entrywise residual-row coefficients. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData
    (D : PeriodicTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualRowCoeff := D.residualRowCoeff
  residual_entry_eq_generatorMap := by
    intro e f
    unfold periodicEdgeKernelResidual5
    exact D.residual_entry_formula e f

/-- Encoded finite-index formulas supply the typed periodic raw scalar formula
data by transporting both kernels through `PeriodicTorus5.edgeEquiv`. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 where
  reggeHessianKernel := encodedToPeriodicEdgeKernel5 D.reggeHessianKernel
  latticeLichnerowiczKernel := encodedToPeriodicEdgeKernel5 D.latticeLichnerowiczKernel
  residualRowCoeff := D.residualRowCoeff
  residual_entry_formula := by
    intro e f
    have h :=
      D.encoded_residual_entry_formula
        (PeriodicTorus5.edgeEquiv.symm e)
        (PeriodicTorus5.edgeEquiv.symm f)
    simpa [encodedToPeriodicEdgeKernel5] using h

/-- Encoded residual-kernel certificates supply encoded raw scalar formula
data. -/
def EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofResidualKernelData
    (D : EncodedTTHessianLichnerowiczResidualKernelFormulaData5) :
    EncodedTTHessianLichnerowiczResidualEntryFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualRowCoeff := D.residualRowCoeff
  encoded_residual_entry_formula := by
    intro e f
    rw [← encodedEdgeKernelResidual5_apply D.reggeHessianKernel D.latticeLichnerowiczKernel e f]
    rw [← D.residualKernel_eq_sub e f]
    exact D.residualKernel_entry_formula e f

/-- Displacement-row certificates supply encoded residual-kernel certificates by
using the edge displacement as the row coefficient index. -/
def EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofDispRowData
    (D : EncodedTTHessianLichnerowiczResidualDispRowFormulaData5) :
    EncodedTTHessianLichnerowiczResidualKernelFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualKernel := D.residualKernel
  residualRowCoeff := fun edge => D.residualDispCoeff edge.disp
  residualKernel_eq_sub := D.residualKernel_eq_sub
  residualKernel_entry_formula := by
    intro e f
    rw [D.residualKernel_row_translation e f]
    exact D.residual_origin_row_formula (PeriodicTorus5.edgeEquiv e).disp f

/-- Seven-row origin-table certificates supply displacement-row certificates. -/
def EncodedTTHessianLichnerowiczResidualDispRowFormulaData5.ofOriginRowTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualDispRowFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualKernel := D.residualKernel
  residualDispCoeff := D.residualDispCoeff
  residualKernel_eq_sub := D.residualKernel_eq_sub
  residualKernel_row_translation := by
    intro e f
    rw [D.residualKernel_row_translation e f]
    rw [D.residualOriginRow_eq_origin]
  residual_origin_row_formula := by
    intro disp f
    rw [← D.residualOriginRow_eq_origin disp f]
    exact D.residualOriginRow_entry_formula disp f

/-- Typed-column origin-table certificates supply seven-row origin-table
certificates. -/
def EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualKernel := D.residualKernel
  residualOriginRow := fun rowDisp f =>
    D.residualOriginColumn
      rowDisp
      (PeriodicTorus5.edgeEquiv f).base
      (PeriodicTorus5.edgeEquiv f).disp
  residualDispCoeff := D.residualDispCoeff
  residualKernel_eq_sub := D.residualKernel_eq_sub
  residualOriginRow_eq_origin := by
    intro rowDisp f
    have hcol :
        ({ base := (PeriodicTorus5.edgeEquiv f).base,
            disp := (PeriodicTorus5.edgeEquiv f).disp } : PeriodicEdge5) =
          PeriodicTorus5.edgeEquiv f := by
      cases PeriodicTorus5.edgeEquiv f
      rfl
    have hidx :
        PeriodicTorus5.edgeEquiv.symm
          ({ base := (PeriodicTorus5.edgeEquiv f).base,
             disp := (PeriodicTorus5.edgeEquiv f).disp } : PeriodicEdge5) = f := by
      rw [hcol]
      simp
    rw [D.residualOriginColumn_eq_origin]
    rw [hidx]
  residualKernel_row_translation := D.residualKernel_row_translation
  residualOriginRow_entry_formula := by
    intro rowDisp f
    simpa using
      D.residualOriginColumn_entry_formula
        rowDisp
        (PeriodicTorus5.edgeEquiv f).base
        (PeriodicTorus5.edgeEquiv f).disp

/-- Raw typed-column certificates supply typed-column origin-table certificates
by using `encodedEdgeKernelResidual5` as the residual matrix. -/
def EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualKernel :=
    encodedEdgeKernelResidual5 D.reggeHessianKernel D.latticeLichnerowiczKernel
  residualOriginColumn := D.residualOriginColumn
  residualDispCoeff := D.residualDispCoeff
  residualKernel_eq_sub := by
    intro e f
    rfl
  residualOriginColumn_eq_origin := by
    intro rowDisp colBase colDisp
    rw [D.residualOriginColumn_eq_sub]
    rfl
  residualKernel_row_translation := D.encodedResidual_row_translation
  residualOriginColumn_entry_formula := D.residualOriginColumn_entry_formula

/-- Coefficient-only origin-column formulas supply raw typed-column
certificates by reconstructing the origin residual table from the generator
map. -/
def EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5.ofCoeffOriginColumnData
    (D : EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5) :
    EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualOriginColumn :=
    fun rowDisp colBase colDisp =>
      periodicTTNormalEquationGeneratorMap5
        (D.residualDispCoeff rowDisp)
        ({ base := colBase, disp := colDisp } : PeriodicEdge5)
  residualDispCoeff := D.residualDispCoeff
  residualOriginColumn_eq_sub := by
    intro rowDisp colBase colDisp
    exact (D.originColumn_entry_formula rowDisp colBase colDisp).symm
  encodedResidual_row_translation := by
    intro e f
    exact D.encodedResidual_entry_formula e f
  residualOriginColumn_entry_formula := by
    intro rowDisp colBase colDisp
    rfl

/-- Translated coefficient-only formulas supply the previous coefficient-only
origin-column certificate by specializing the translated formula to the origin
edge. -/
def EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5.ofCoeffTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffTranslatedFormulaData5) :
    EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualDispCoeff := D.residualDispCoeff
  originColumn_entry_formula := by
    intro rowDisp colBase colDisp
    have h :=
      D.encodedResidual_entry_formula
        (encodedOriginEdgeOfDisp5 rowDisp)
        (PeriodicTorus5.edgeEquiv.symm
          ({ base := colBase, disp := colDisp } : PeriodicEdge5))
    simpa [encodedEdgeKernelResidual5, encodedOriginEdgeOfDisp5_equiv] using h
  encodedResidual_entry_formula := D.encodedResidual_entry_formula

/-- Relative translated coefficient-only formulas specialize to the same
origin-column formulas as the absolute translated surface.  This is only an
origin-row consequence: it does not assert the stronger absolute row formula. -/
def EncodedTTHessianLichnerowiczCoeffRelativeOriginColumnFormulaData5.ofCoeffRelativeTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5) :
    EncodedTTHessianLichnerowiczCoeffRelativeOriginColumnFormulaData5 where
  reggeHessianKernel := D.reggeHessianKernel
  latticeLichnerowiczKernel := D.latticeLichnerowiczKernel
  residualDispCoeff := D.residualDispCoeff
  originColumn_entry_formula := by
    intro rowDisp colBase colDisp
    have h :=
      D.encodedResidual_relative_entry_formula
        (encodedOriginEdgeOfDisp5 rowDisp)
        (PeriodicTorus5.edgeEquiv.symm
          ({ base := colBase, disp := colDisp } : PeriodicEdge5))
    simpa [encodedEdgeKernelResidual5, encodedOriginEdgeOfDisp5_equiv,
      periodicRelativeColumnOfOriginDisp5] using h

/-- Raw typed-column certificates supply seven-row origin-table certificates. -/
def EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData
    (EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData D)

/-- Seven-row origin-table certificates supply encoded residual-kernel
certificates. -/
def EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofOriginRowTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualKernelFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofDispRowData
    (EncodedTTHessianLichnerowiczResidualDispRowFormulaData5.ofOriginRowTableData D)

/-- Typed-column origin-table certificates supply encoded residual-kernel
certificates. -/
def EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofOriginColumnTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualKernelFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofOriginRowTableData
    (EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData D)

/-- Raw typed-column certificates supply encoded residual-kernel certificates. -/
def EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    EncodedTTHessianLichnerowiczResidualKernelFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofOriginColumnTableData
    (EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData D)

/-- Displacement-row certificates supply encoded raw scalar formula data. -/
def EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofDispRowData
    (D : EncodedTTHessianLichnerowiczResidualDispRowFormulaData5) :
    EncodedTTHessianLichnerowiczResidualEntryFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofResidualKernelData
    (EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofDispRowData D)

/-- Seven-row origin-table certificates supply encoded raw scalar formula data. -/
def EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginRowTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualEntryFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofDispRowData
    (EncodedTTHessianLichnerowiczResidualDispRowFormulaData5.ofOriginRowTableData D)

/-- Typed-column origin-table certificates supply encoded raw scalar formula
data. -/
def EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginColumnTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5) :
    EncodedTTHessianLichnerowiczResidualEntryFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginRowTableData
    (EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData D)

/-- Raw typed-column certificates supply encoded raw scalar formula data. -/
def EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    EncodedTTHessianLichnerowiczResidualEntryFormulaData5 :=
  EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginColumnTableData
    (EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData D)


/-- Encoded residual-kernel certificates supply the typed periodic raw scalar
formula data. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedResidualKernelData
    (D : EncodedTTHessianLichnerowiczResidualKernelFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 :=
  PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData
    (EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofResidualKernelData D)

/-- Displacement-row certificates supply the typed periodic raw scalar formula
data. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofDispRowData
    (D : EncodedTTHessianLichnerowiczResidualDispRowFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 :=
  PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedResidualKernelData
    (EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofDispRowData D)

/-- Seven-row origin-table certificates supply the typed periodic raw scalar
formula data. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginRowTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 :=
  PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofDispRowData
    (EncodedTTHessianLichnerowiczResidualDispRowFormulaData5.ofOriginRowTableData D)

/-- Typed-column origin-table certificates supply the typed periodic raw scalar
formula data. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginColumnTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 :=
  PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginRowTableData
    (EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData D)

/-- Raw typed-column certificates supply the typed periodic raw scalar formula
data. -/
def PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualEntryFormulaData5 :=
  PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofOriginColumnTableData
    (EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData D)



/-- Encoded finite-index formulas supply entrywise residual-row coefficients. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5 :=
  PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData
    (PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData D)

/-- Encoded residual-kernel certificates supply entrywise residual-row
coefficients. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofEncodedResidualKernelData
    (D : EncodedTTHessianLichnerowiczResidualKernelFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5 :=
  PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofEncodedData
    (EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofResidualKernelData D)

/-- Raw scalar residual formulas supply row-coefficient data. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofFormulaData
    (D : PeriodicTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffData5 :=
  PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEntryData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData D)

/-- Encoded finite-index formulas supply row-coefficient data. -/
def PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowCoeffData5 :=
  PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofFormulaData
    (PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData D)

/-- Entrywise residual-row coefficients supply residual-row span data. -/
def PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofEntryCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5) :
    PeriodicTTHessianLichnerowiczResidualRowSpanData5 :=
  PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofRowCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEntryData D)

/-- Raw scalar residual formulas supply residual-row span data. -/
def PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofFormulaData
    (D : PeriodicTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowSpanData5 :=
  PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofEntryCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData D)

/-- Encoded finite-index formulas supply residual-row span data. -/
def PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczResidualRowSpanData5 :=
  PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofFormulaData
    (PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData D)

/-- Explicit residual-row coefficients supply residual-kernel zero-on-TT data. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofRowCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofResidualRowSpanData
    (PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofRowCoeffData D)

/-- Entrywise residual-row coefficients supply residual-kernel zero-on-TT data. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofEntryCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofRowCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEntryData D)

/-- Raw scalar residual formulas supply residual-kernel zero-on-TT data. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofFormulaData
    (D : PeriodicTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofEntryCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData D)

/-- Encoded finite-index formulas supply residual-kernel zero-on-TT data. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofFormulaData
    (PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData D)

/-- Relative-frame translated certificates prove residual-kernel zero on TT once
the shifted-generator orthogonality lemma is supplied. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedTTZeroData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 where
  reggeHessianKernel := encodedToPeriodicEdgeKernel5 D.relativeData.reggeHessianKernel
  latticeLichnerowiczKernel := encodedToPeriodicEdgeKernel5 D.relativeData.latticeLichnerowiczKernel
  residual_zero_on_tt := by
    intro ε hε
    funext row
    rw [periodicEdgeKernelOperator5_eq_inner_row]
    have hrow :
        periodicEdgeKernelRowVector5
          (periodicEdgeKernelResidual5
            (encodedToPeriodicEdgeKernel5 D.relativeData.reggeHessianKernel)
            (encodedToPeriodicEdgeKernel5 D.relativeData.latticeLichnerowiczKernel))
          row =
        periodicRelativeTTNormalEquationGeneratorMap5 row
          (D.relativeData.residualDispCoeff row.disp) := by
      funext col
      unfold periodicEdgeKernelRowVector5 periodicEdgeKernelResidual5
        encodedToPeriodicEdgeKernel5 periodicRelativeTTNormalEquationGeneratorMap5
      simpa [encodedEdgeKernelResidual5] using
        D.relativeData.encodedResidual_relative_entry_formula
        (PeriodicTorus5.edgeEquiv.symm row)
        (PeriodicTorus5.edgeEquiv.symm col)
    rw [hrow]
    exact D.relativeGeneratorOrthogonalOnTT ε hε row
      (D.relativeData.residualDispCoeff row.disp)

/-- Relative-frame translated closure data proves residual-kernel zero on TT. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedClosureData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedClosureData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedTTZeroData
    (EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5.ofClosureData D)

/-- Relative-frame translated certificates prove residual-kernel zero on TT
unconditionally, because the shifted-generator closure theorem is proved above. -/
def PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5) :
    PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5 :=
  PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedTTZeroData
    (EncodedTTHessianLichnerowiczCoeffRelativeTranslatedTTZeroData5.ofRelativeTranslatedData D)

/-- Entrywise kernel data supplies the TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofKernelEntryData
    (D : PeriodicTTHessianLichnerowiczKernelEntryData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofKernelRowData
    (PeriodicTTHessianLichnerowiczKernelRowData5.ofEntryData D)

/-- Residual-kernel vanishing on TT perturbations supplies the TT
Hessian/Lichnerowicz operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofResidualTTZeroData
    (D : PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofKernelRowData
    (PeriodicTTHessianLichnerowiczKernelRowData5.ofResidualTTZeroData D)

/-- Relative-frame translated coefficient certificates supply TT
Hessian/Lichnerowicz operator-match data through the proved shifted-generator
closure theorem. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofResidualTTZeroData
    (PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofCoeffRelativeTranslatedData D)

/-- Residual-row generator-span data supplies the TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofResidualRowSpanData
    (D : PeriodicTTHessianLichnerowiczResidualRowSpanData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofResidualTTZeroData
    (PeriodicTTHessianLichnerowiczKernelResidualTTZeroData5.ofResidualRowSpanData D)

/-- Explicit residual-row coefficients supply TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofRowCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofResidualRowSpanData
    (PeriodicTTHessianLichnerowiczResidualRowSpanData5.ofRowCoeffData D)

/-- Entrywise residual-row coefficients supply TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofEntryCoeffData
    (D : PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofRowCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffData5.ofEntryData D)

/-- Raw scalar residual formulas supply TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofFormulaData
    (D : PeriodicTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofEntryCoeffData
    (PeriodicTTHessianLichnerowiczResidualRowCoeffEntryData5.ofFormulaData D)

/-- Encoded finite-index formulas supply TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofEncodedData
    (D : EncodedTTHessianLichnerowiczResidualEntryFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofFormulaData
    (PeriodicTTHessianLichnerowiczResidualEntryFormulaData5.ofEncodedData D)

/-- Encoded residual-kernel certificates supply TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofEncodedResidualKernelData
    (D : EncodedTTHessianLichnerowiczResidualKernelFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofEncodedData
    (EncodedTTHessianLichnerowiczResidualEntryFormulaData5.ofResidualKernelData D)

/-- Displacement-row certificates supply TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofDispRowData
    (D : EncodedTTHessianLichnerowiczResidualDispRowFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofEncodedResidualKernelData
    (EncodedTTHessianLichnerowiczResidualKernelFormulaData5.ofDispRowData D)

/-- Seven-row origin-table certificates supply TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofOriginRowTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofDispRowData
    (EncodedTTHessianLichnerowiczResidualDispRowFormulaData5.ofOriginRowTableData D)

/-- Typed-column origin-table certificates supply TT Hessian/Lichnerowicz
operator-match data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofOriginColumnTableData
    (D : EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofOriginRowTableData
    (EncodedTTHessianLichnerowiczResidualOriginRowTableFormulaData5.ofOriginColumnTableData D)

/-- Raw typed-column certificates supply TT Hessian/Lichnerowicz operator-match
data. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofRawOriginColumnData
    (D : EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofOriginColumnTableData
    (EncodedTTHessianLichnerowiczResidualOriginColumnTableFormulaData5.ofRawOriginColumnData D)

/-- Coefficient-only origin-column certificates supply TT Hessian/Lichnerowicz
operator-match data by reconstructing the raw typed-column certificate. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData
    (D : EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofRawOriginColumnData
    (EncodedTTHessianLichnerowiczRawOriginColumnFormulaData5.ofCoeffOriginColumnData D)

/-- Translated coefficient-only certificates supply TT Hessian/Lichnerowicz
operator-match data through the derived coefficient origin-column certificate. -/
def PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData
    (D : EncodedTTHessianLichnerowiczCoeffTranslatedFormulaData5) :
    PeriodicTTHessianLichnerowiczMatchData5 :=
  PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData
    (EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5.ofCoeffTranslatedData D)

/-- Operator equality on TT modes gives equality of the associated bilinear
forms whenever the right input is TT. -/
theorem periodicTTHessianLichnerowicz_bilinear_eq_of_matchData5
    (D : PeriodicTTHessianLichnerowiczMatchData5)
    (ε η : PeriodicEdgePerturbation5)
    (hη : PeriodicLongitudinalTTSubspace5 η) :
    periodicTTOperatorBilinear5 D.reggeHessianTT ε η =
      periodicTTOperatorBilinear5 D.latticeLichnerowiczTT ε η := by
  unfold periodicTTOperatorBilinear5
  rw [D.matches_on_tt η hη]

/-- Operator equality on TT modes gives equality of the quadratic TT energy. -/
theorem periodicTTHessianLichnerowicz_quadratic_eq_of_matchData5
    (D : PeriodicTTHessianLichnerowiczMatchData5)
    (ε : PeriodicEdgePerturbation5)
    (hε : PeriodicLongitudinalTTSubspace5 ε) :
    periodicTTOperatorBilinear5 D.reggeHessianTT ε ε =
      periodicTTOperatorBilinear5 D.latticeLichnerowiczTT ε ε :=
  periodicTTHessianLichnerowicz_bilinear_eq_of_matchData5 D ε ε hε

/-- Coefficient-only origin-column certificates give equality of the associated
bilinear forms whenever the right input is TT. -/
theorem periodicTTHessianLichnerowicz_bilinear_eq_of_coeffOriginColumnData5
    (D : EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5)
    (ε η : PeriodicEdgePerturbation5)
    (hη : PeriodicLongitudinalTTSubspace5 η) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D).reggeHessianTT ε η =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D).latticeLichnerowiczTT ε η :=
  periodicTTHessianLichnerowicz_bilinear_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D) ε η hη

/-- Coefficient-only origin-column certificates give equality of the quadratic
TT energy. -/
theorem periodicTTHessianLichnerowicz_quadratic_eq_of_coeffOriginColumnData5
    (D : EncodedTTHessianLichnerowiczCoeffOriginColumnFormulaData5)
    (ε : PeriodicEdgePerturbation5)
    (hε : PeriodicLongitudinalTTSubspace5 ε) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D).reggeHessianTT ε ε =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D).latticeLichnerowiczTT ε ε :=
  periodicTTHessianLichnerowicz_quadratic_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffOriginColumnData D) ε hε

/-- Translated coefficient-only certificates give equality of the associated
bilinear forms whenever the right input is TT. -/
theorem periodicTTHessianLichnerowicz_bilinear_eq_of_coeffTranslatedData5
    (D : EncodedTTHessianLichnerowiczCoeffTranslatedFormulaData5)
    (ε η : PeriodicEdgePerturbation5)
    (hη : PeriodicLongitudinalTTSubspace5 η) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D).reggeHessianTT ε η =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D).latticeLichnerowiczTT ε η :=
  periodicTTHessianLichnerowicz_bilinear_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D) ε η hη

/-- Translated coefficient-only certificates give equality of the quadratic TT
energy. -/
theorem periodicTTHessianLichnerowicz_quadratic_eq_of_coeffTranslatedData5
    (D : EncodedTTHessianLichnerowiczCoeffTranslatedFormulaData5)
    (ε : PeriodicEdgePerturbation5)
    (hε : PeriodicLongitudinalTTSubspace5 ε) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D).reggeHessianTT ε ε =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D).latticeLichnerowiczTT ε ε :=
  periodicTTHessianLichnerowicz_quadratic_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffTranslatedData D) ε hε

/-- Relative-frame translated coefficient-only certificates give equality of the
associated bilinear forms whenever the right input is TT. -/
theorem periodicTTHessianLichnerowicz_bilinear_eq_of_coeffRelativeTranslatedData5
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5)
    (ε η : PeriodicEdgePerturbation5)
    (hη : PeriodicLongitudinalTTSubspace5 η) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D).reggeHessianTT ε η =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D).latticeLichnerowiczTT ε η :=
  periodicTTHessianLichnerowicz_bilinear_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D) ε η hη

/-- Relative-frame translated coefficient-only certificates give equality of the
quadratic TT energy. -/
theorem periodicTTHessianLichnerowicz_quadratic_eq_of_coeffRelativeTranslatedData5
    (D : EncodedTTHessianLichnerowiczCoeffRelativeTranslatedFormulaData5)
    (ε : PeriodicEdgePerturbation5)
    (hε : PeriodicLongitudinalTTSubspace5 ε) :
    periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D).reggeHessianTT ε ε =
      periodicTTOperatorBilinear5
        (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D).latticeLichnerowiczTT ε ε :=
  periodicTTHessianLichnerowicz_quadratic_eq_of_matchData5
    (PeriodicTTHessianLichnerowiczMatchData5.ofCoeffRelativeTranslatedData D) ε hε

theorem periodicFreudenthalTTOrthogonalDecompositionTargetAtN5_to_target
    (GaugePotential : Type) (gaugeMap : GaugePotential → PeriodicEdgePerturbation5) :
    PeriodicFreudenthalTTOrthogonalDecompositionTargetAtN5 GaugePotential gaugeMap →
      PeriodicFreudenthalTTDecompositionTargetAtN5
        PeriodicConformalLogSubspace5
        (PeriodicGaugeSubspace5 GaugePotential gaugeMap)
        (PeriodicTTOrthogonal5 GaugePotential gaugeMap) := by
  intro h
  exact h

/-- Session 215 scaffold endpoint for Track 1.D. -/
def Track1DTensorShearScaffoldEndpoint : Prop :=
  Nonempty (∀ K : Triangulation3D, VertexPotential K → EdgePerturbation K) ∧
    Nonempty (EncodedEdgePerturbation5 ≃ PeriodicEdgePerturbation5) ∧
    (∀ h v : ℝ, h ≠ v →
      ¬ ∃ ξa ξb ξc ξd : ℝ,
        (ξa + ξb) / 2 = h ∧
        (ξc + ξd) / 2 = h ∧
        (ξb + ξc) / 2 = v ∧
        (ξd + ξa) / 2 = v)

theorem track1D_tensorShearScaffoldEndpoint_holds :
    Track1DTensorShearScaffoldEndpoint := by
  constructor
  · exact ⟨fun K => conformalEdgeLogStrain K⟩
  · constructor
    · exact ⟨periodicEdgePerturbationEquiv5⟩
    · intro h v hne
      exact nontrivial_rectangle_shear_not_vertexConformal h v hne

end

end TensorShearSector
end Gravity
end IndisputableMonolith
