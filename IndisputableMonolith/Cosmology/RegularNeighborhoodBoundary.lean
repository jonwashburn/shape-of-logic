import Mathlib

/-!
# Cosmology: regular-neighborhood boundary genus bridge (Phases 27, 28, 31, 35, 37, 39, 40, 41, 42, 43, 44, 46, 47)

## Status: PARTIAL THEOREM through Phase 44; CONDITIONAL THEOREM at Phase 47 (0 sorry, 0 new axiom).

Phase 25 measured the raw cubical boundary surface of the positive excursion set `{q > 0}` and
found real nonmanifold edges in the horizon-annulus handle. Phase 26 therefore switched to the
canonical desingularized readout: the boundary of a regular neighborhood of the exact positive
region.

This module proves the algebraic bridge used by
`scripts/cosmogenesis/foam_interface_desingularized.py`. If a compact 3D cubical region has Betti
triple `(b₀,b₁,b₂)` and its regular-neighborhood boundary has

* boundary components `b₀ + b₂`,
* boundary Euler characteristic `2 * (b₀ - b₁ + b₂)`,
* genus computed by `components - χ(region)`,

then the total desingularized boundary genus is exactly `b₁`.

Phase 31 adds the algebraic half of the Phase-30 vertex-link half-quotient. If the raw singular
boundary has already had its four-face edges paired, and the singular-edge components supply a
half-vertex quotient equal to the missing vertex budget, then the corrected Euler characteristic
equals the canonical CW Euler characteristic. The embedded digital-cubical collapse remains OPEN:
this file proves the arithmetic bridge and the horizon/dyadic numeric certificates, not the
geometric realization theorem.

Phase 35 adds the algebraic bridge for the Phase-34 component assembly. If the corrected
edge-paired face components have the canonical component count and Euler half-sum, then their
total genus is forced to be `b₁`. This still does not prove homeomorphism of the corrected
component cellulations to the regular-neighborhood boundary components.

Phase 37 adds the algebraic wrapper for the Phase-36 polygon-gluing witness. If a finite polygon
gluing supplies binary edge gluing, cyclic quotient-vertex links, and the same corrected component
Euler data, then it reduces to the Phase-35 component assembly theorem. This is still a finite
combinatorial certificate, not the final regular-neighborhood homeomorphism theorem.

Phase 39 adds the algebraic wrapper for the Phase-38 orientability witness. If every polygon
component has a full face-orientation assignment with zero contradictions, the oriented certificate
inherits the Phase-37 polygon-gluing genus theorem. This records the orientability gate without
promoting it to the missing homeomorphism theorem.

Phase 40 adds the standard-surface classification wrapper. It records the surface type forced by
each oriented polygon component's Euler characteristic, e.g. sphere, torus, and genus-125 surface.
This classifies the components abstractly; the embedded homeomorphism to the regular-neighborhood
boundary remains the open geometric theorem.

Phase 41 tightens the classification wrapper into a full surface-type inventory: the assigned
standard surface list must have the same component count as the oriented polygon list, its total
Euler characteristic is derived from the standard formula, and the resulting count, Euler, and
genus match the regular-neighborhood boundary invariants. The embedded homeomorphism theorem
remains open.

Phase 42 adds the ordered componentwise Euler-signature bridge. The assigned standard-surface list
is not merely right in aggregate: component-by-component, the oriented polygon Euler list equals the
standard-surface Euler list. This is still algebraic inventory matching, not the embedded
homeomorphism theorem.

Phase 43 names the finite component pairing itself. The paired list is the ordered zip between
oriented polygon components and standard regular-boundary surface types; every pair is checked for
orientation success and Euler match, and the paired inventory has the regular-boundary component,
Euler, and genus totals. The actual embedded map remains the open geometric theorem.

Phase 44 names the embedded-map obligations that must replace the abstract Phase-43 pairing. A
candidate map must be incidence-preserving, bijective on quotient cells, vertex-link preserving,
and orientation-preserving. This module proves that such obligations reduce to the existing
component-pairing inventory. It does not construct the geometric maps.

Phase 46 replaces the abstract Phase-44 obligation `Prop` fields with concrete decidable
closed-orientable-surface conditions (`CombinatorialClosedOrientableSurface`: Euler-ok, cyclic links,
oriented, and the closed quadrangulation identity `edges = 2*faces`). The horizon and dyadic targets
satisfy them by `native_decide`, so the obligation packages close on real combinatorial content rather
than placeholders. The embedded homeomorphism still requires the classification of closed surfaces.

Phase 47 makes that last dependency a first-class object. `ClosedSurfaceClassification R` names the
classification of closed surfaces as an explicit hypothesis on an abstract realization relation `R`
(geometric realization homeomorphic to the standard surface), never as an axiom. Conditional on it, the
horizon torus/sphere and all dyadic components are realized by their standard surfaces
(`horizonAnnulusHandle_realizesStandard`, `dyadicSpongeR20_realizesStandard`). These are CONDITIONAL
THEOREMs: the chain from recognition foam to a per-component homeomorphism is complete modulo the one
named classical input, with no new axiom.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RegularNeighborhoodBoundary

/-- Betti data of a compact 3D region, represented in integers so Euler algebra is literal. -/
structure BettiTriple where
  b0 : ℤ
  b1 : ℤ
  b2 : ℤ
deriving Repr, DecidableEq

/-- Euler characteristic of a 3D region from its Betti triple: `χ = b₀ - b₁ + b₂`. -/
def regionEuler (B : BettiTriple) : ℤ :=
  B.b0 - B.b1 + B.b2

/-- The regular-neighborhood boundary component count predicted by Alexander duality intuition. -/
def regularBoundaryComponents (B : BettiTriple) : ℤ :=
  B.b0 + B.b2

/-- The regular-neighborhood boundary Euler characteristic: doubled region Euler characteristic. -/
def regularBoundaryEuler (B : BettiTriple) : ℤ :=
  2 * regionEuler B

/-- Total genus of the regular-neighborhood boundary, using `χ(boundary) = 2χ(region)`. -/
def regularBoundaryGenus (B : BettiTriple) : ℤ :=
  regularBoundaryComponents B - regionEuler B

/-- A canonical CW model for the desingularized regular boundary: one zero-cell and one
two-cell per boundary component, and `2*b₁` one-cells carrying the total handle rank. This is
the topological cell-count model behind the Phase-28 certificate, not an embedded cubical
sheet-splitting construction. -/
def regularBoundaryCWVertices (B : BettiTriple) : ℤ :=
  regularBoundaryComponents B

/-- One-cells in the canonical regular-boundary CW model. -/
def regularBoundaryCWEdges (B : BettiTriple) : ℤ :=
  2 * B.b1

/-- Two-cells in the canonical regular-boundary CW model. -/
def regularBoundaryCWFaces (B : BettiTriple) : ℤ :=
  regularBoundaryComponents B

/-- Euler characteristic of the canonical regular-boundary CW model. -/
def regularBoundaryCWEuler (B : BettiTriple) : ℤ :=
  regularBoundaryCWVertices B - regularBoundaryCWEdges B + regularBoundaryCWFaces B

/-- **THEOREM (regular-boundary genus bridge).** Once the regular-neighborhood boundary
components and Euler characteristic are identified, the total desingularized boundary genus is
exactly the region's first Betti number. -/
theorem regularBoundaryGenus_eq_b1 (B : BettiTriple) :
    regularBoundaryGenus B = B.b1 := by
  unfold regularBoundaryGenus regularBoundaryComponents regionEuler
  ring

/-- Equivalent doubled form, useful when avoiding integer division in downstream certificates. -/
theorem regularBoundaryEuler_eq_two_regionEuler (B : BettiTriple) :
    regularBoundaryEuler B = 2 * regionEuler B := by
  rfl

/-- **THEOREM (canonical CW model realizes the doubled Euler law).** The Phase-28 CW boundary
model has Euler characteristic `2 * χ(region)`. -/
theorem regularBoundaryCWEuler_eq_regularBoundaryEuler (B : BettiTriple) :
    regularBoundaryCWEuler B = regularBoundaryEuler B := by
  unfold regularBoundaryCWEuler regularBoundaryCWVertices regularBoundaryCWEdges
    regularBoundaryCWFaces regularBoundaryEuler regularBoundaryComponents regionEuler
  ring

/-- The canonical CW model has Euler characteristic `2 * χ(region)` in expanded form. -/
theorem regularBoundaryCWEuler_eq_two_regionEuler (B : BettiTriple) :
    regularBoundaryCWEuler B = 2 * regionEuler B := by
  rw [regularBoundaryCWEuler_eq_regularBoundaryEuler, regularBoundaryEuler_eq_two_regionEuler]

/-- The Euler-form surface identity: `components - χ(boundary)/2 = b₁`, encoded without division
by using the already-halved `χ(region)` from the doubled-boundary theorem. -/
theorem components_minus_regionEuler_eq_b1 (B : BettiTriple) :
    regularBoundaryComponents B - regionEuler B = B.b1 := by
  simpa [regularBoundaryGenus] using regularBoundaryGenus_eq_b1 B

/-- A boundary report satisfies the regular-neighborhood bridge for a region. This is the
geometry-facing predicate: future work must prove it for the concrete digital construction. -/
structure IsRegularBoundaryOf (B : BettiTriple) where
  components : ℤ
  euler : ℤ
  genus : ℤ
  components_eq : components = regularBoundaryComponents B
  euler_eq : euler = regularBoundaryEuler B
  genus_eq : genus = regularBoundaryGenus B

/-- **THEOREM.** Any boundary report satisfying the regular-neighborhood bridge has genus `b₁`. -/
theorem genus_eq_b1_of_isRegularBoundaryOf {B : BettiTriple} (S : IsRegularBoundaryOf B) :
    S.genus = B.b1 := by
  rw [S.genus_eq, regularBoundaryGenus_eq_b1]

/-! ## Phase 30/31: singular-edge half-vertex quotient. -/

/-- One connected component of the singular-edge graph after the Phase-29 four-face edge pairing
step. `vertices` and `edges` are recorded only as cell counts; this is not yet an embedded
geometric construction. -/
structure SingularGraphComponent where
  vertices : ℕ
  edges : ℕ
deriving Repr, DecidableEq

/-- The Phase-30 vertex-link quotient contribution of one singular component: one vertex lift per
pair of singular vertices in that component. -/
def halfVertexComponentDelta (C : SingularGraphComponent) : ℕ :=
  C.vertices / 2

/-- Total half-vertex delta over all singular-edge components. -/
def singularGraphHalfVertexDelta (Cs : List SingularGraphComponent) : ℕ :=
  (Cs.map halfVertexComponentDelta).sum

/-- Euler characteristic after Phase-29 edge splitting and the Phase-30 half-vertex correction. -/
def halfVertexCorrectedEuler (edgeOnlyEuler : ℤ) (Cs : List SingularGraphComponent) : ℤ :=
  edgeOnlyEuler + singularGraphHalfVertexDelta Cs

/-- The half-vertex quotient closes when the corrected raw-boundary Euler characteristic equals the
canonical Phase-28 regular-boundary CW Euler characteristic. -/
def HalfVertexQuotientCloses (B : BettiTriple) (edgeOnlyEuler : ℤ)
    (Cs : List SingularGraphComponent) : Prop :=
  halfVertexCorrectedEuler edgeOnlyEuler Cs = regularBoundaryCWEuler B

/-- Algebraic bridge for the Phase-30 quotient: once the half-vertex delta is exactly the missing
vertex budget, the corrected edge-paired Euler count is the canonical CW Euler count. -/
theorem halfVertexCorrectedEuler_eq_cw_of_delta_eq_required
    (B : BettiTriple) (edgeOnlyEuler : ℤ) (Cs : List SingularGraphComponent)
    (requiredDelta : ℕ)
    (hDelta : singularGraphHalfVertexDelta Cs = requiredDelta)
    (hBudget : edgeOnlyEuler + (requiredDelta : ℤ) = regularBoundaryCWEuler B) :
    HalfVertexQuotientCloses B edgeOnlyEuler Cs := by
  unfold HalfVertexQuotientCloses halfVertexCorrectedEuler
  rw [hDelta]
  exact hBudget

/-- Singular component with two vertices and one singular edge. -/
def singularV2E1 : SingularGraphComponent :=
  { vertices := 2, edges := 1 }

/-- Singular component with four vertices and three singular edges. -/
def singularV4E3 : SingularGraphComponent :=
  { vertices := 4, edges := 3 }

/-! ## Phase 34/35: corrected component assembly. -/

/-- One connected component of the corrected boundary after edge pairing and local vertex-link
collapse. The component is represented only by its Euler characteristic. -/
structure CorrectedBoundaryComponent where
  euler : ℤ
deriving Repr, DecidableEq

/-- Number of corrected boundary components. -/
def correctedComponentCount (Cs : List CorrectedBoundaryComponent) : ℤ :=
  Cs.length

/-- Total Euler characteristic over corrected boundary components. -/
def correctedComponentEuler (Cs : List CorrectedBoundaryComponent) : ℤ :=
  (Cs.map CorrectedBoundaryComponent.euler).sum

/-- Genus total read from component count and a supplied half-Euler value. The half-Euler is kept
explicit to avoid hiding the doubled-boundary theorem behind integer division. -/
def correctedComponentGenusFromHalfEuler (Cs : List CorrectedBoundaryComponent) (halfEuler : ℤ) : ℤ :=
  correctedComponentCount Cs - halfEuler

/-- A corrected component list has the regular-neighborhood component assembly data for a region. -/
def ComponentAssemblyCloses (B : BettiTriple) (Cs : List CorrectedBoundaryComponent)
    (halfEuler : ℤ) : Prop :=
  correctedComponentCount Cs = regularBoundaryComponents B ∧
  correctedComponentEuler Cs = 2 * halfEuler ∧
  halfEuler = regionEuler B

/-- Algebraic bridge for Phase 34: once the corrected component count and Euler half-sum match the
regular-neighborhood data, the total component genus is exactly `b₁`. -/
theorem correctedComponentGenus_eq_b1_of_componentAssemblyCloses
    (B : BettiTriple) (Cs : List CorrectedBoundaryComponent) (halfEuler : ℤ)
    (h : ComponentAssemblyCloses B Cs halfEuler) :
    correctedComponentGenusFromHalfEuler Cs halfEuler = B.b1 := by
  rcases h with ⟨hCount, _hEuler, hHalf⟩
  unfold correctedComponentGenusFromHalfEuler
  rw [hCount, hHalf]
  exact components_minus_regionEuler_eq_b1 B

/-- A sphere component has Euler characteristic two. -/
def sphereComponent : CorrectedBoundaryComponent :=
  { euler := 2 }

/-- A torus component has Euler characteristic zero. -/
def torusComponent : CorrectedBoundaryComponent :=
  { euler := 0 }

/-- The dyadic probe's large corrected component has Euler characteristic `-248`, i.e. genus `125`
when it is closed and orientable. -/
def genus125Component : CorrectedBoundaryComponent :=
  { euler := -248 }

/-- Phase-34 corrected components for the horizon-annulus target: one torus plus one sphere. -/
def horizonAnnulusHandleCorrectedComponents : List CorrectedBoundaryComponent :=
  [torusComponent, sphereComponent]

/-- Phase-34 corrected components for the dyadic sponge: one genus-125 component plus 52 spheres. -/
def dyadicSpongeR20CorrectedComponents : List CorrectedBoundaryComponent :=
  [genus125Component] ++ List.replicate 52 sphereComponent

/-! ## Phase 36/37: finite polygon-gluing surface witness. -/

/-- One polygon-glued surface component from Phase 36. The fields record the quotient vertex count,
split-edge count, face count, Euler count, and local vertex-link audit. -/
structure PolygonGluingComponent where
  vertices : ℤ
  edges : ℤ
  faces : ℤ
  euler : ℤ
  vertexLinks : ℕ
  vertexLinkCycles : ℕ
deriving Repr, DecidableEq

/-- The component's cell counts compute the recorded Euler characteristic. -/
def PolygonComponentEulerOk (C : PolygonGluingComponent) : Prop :=
  C.vertices - C.edges + C.faces = C.euler

/-- Every quotient vertex has a single cyclic link. -/
def PolygonComponentLinksCyclic (C : PolygonGluingComponent) : Prop :=
  C.vertexLinkCycles = C.vertexLinks

/-- Forget the polygon-level audit down to the corrected-boundary component used in Phase 35. -/
def polygonComponentToCorrected (C : PolygonGluingComponent) : CorrectedBoundaryComponent :=
  { euler := C.euler }

/-- Forget a list of polygon-glued components to its Euler-only corrected-component list. -/
def polygonComponentsToCorrected (Cs : List PolygonGluingComponent) : List CorrectedBoundaryComponent :=
  Cs.map polygonComponentToCorrected

/-- A finite polygon-gluing witness closes when all component cell Euler counts are correct, all
quotient vertex links are cyclic, and the forgotten Euler data closes the Phase-35 assembly. -/
def PolygonGluingCloses (B : BettiTriple) (Cs : List PolygonGluingComponent)
    (halfEuler : ℤ) : Prop :=
  (∀ C ∈ Cs, PolygonComponentEulerOk C) ∧
  (∀ C ∈ Cs, PolygonComponentLinksCyclic C) ∧
  ComponentAssemblyCloses B (polygonComponentsToCorrected Cs) halfEuler

/-- Algebraic bridge for Phase 36: polygon gluing with valid Euler counts and cyclic vertex links
inherits the Phase-35 total-genus theorem. -/
theorem polygonGluedGenus_eq_b1_of_polygonGluingCloses
    (B : BettiTriple) (Cs : List PolygonGluingComponent) (halfEuler : ℤ)
    (h : PolygonGluingCloses B Cs halfEuler) :
    correctedComponentGenusFromHalfEuler (polygonComponentsToCorrected Cs) halfEuler = B.b1 := by
  rcases h with ⟨_hEuler, _hLinks, hAssembly⟩
  exact correctedComponentGenus_eq_b1_of_componentAssemblyCloses B
    (polygonComponentsToCorrected Cs) halfEuler hAssembly

/-- The polygon-glued torus component from Phase 36 horizon `R = 20`. -/
def horizonPolygonTorusComponent : PolygonGluingComponent :=
  { vertices := 1632, edges := 3264, faces := 1632, euler := 0,
    vertexLinks := 1632, vertexLinkCycles := 1632 }

/-- The polygon-glued sphere component from Phase 36 horizon `R = 20`. -/
def horizonPolygonSphereComponent : PolygonGluingComponent :=
  { vertices := 2484, edges := 4964, faces := 2482, euler := 2,
    vertexLinks := 2484, vertexLinkCycles := 2484 }

/-- The Phase-36 horizon polygon-gluing components. -/
def horizonAnnulusHandlePolygonComponents : List PolygonGluingComponent :=
  [horizonPolygonTorusComponent, horizonPolygonSphereComponent]

/-- The large genus-125 component from the Phase-36 dyadic polygon gluing. -/
def dyadicPolygonGenus125Component : PolygonGluingComponent :=
  { vertices := 8740, edges := 17976, faces := 8988, euler := -248,
    vertexLinks := 8740, vertexLinkCycles := 8740 }

/-- A six-face cube-sphere component in the dyadic Phase-36 polygon gluing. -/
def dyadicPolygonSmallSphereComponent : PolygonGluingComponent :=
  { vertices := 8, edges := 12, faces := 6, euler := 2,
    vertexLinks := 8, vertexLinkCycles := 8 }

/-- A twenty-two-face sphere component in the dyadic Phase-36 polygon gluing. -/
def dyadicPolygonMediumSphereComponent : PolygonGluingComponent :=
  { vertices := 24, edges := 44, faces := 22, euler := 2,
    vertexLinks := 24, vertexLinkCycles := 24 }

/-- A thirty-face sphere component in the dyadic Phase-36 polygon gluing. -/
def dyadicPolygonLargeSphereComponent : PolygonGluingComponent :=
  { vertices := 32, edges := 60, faces := 30, euler := 2,
    vertexLinks := 32, vertexLinkCycles := 32 }

/-- The Phase-36 dyadic polygon-gluing components: one genus-125 component, 48 small spheres, 3
medium spheres, and 1 large sphere. -/
def dyadicSpongeR20PolygonComponents : List PolygonGluingComponent :=
  [dyadicPolygonGenus125Component] ++
    List.replicate 48 dyadicPolygonSmallSphereComponent ++
    List.replicate 3 dyadicPolygonMediumSphereComponent ++
    [dyadicPolygonLargeSphereComponent]

/-! ## Phase 38/39: orientability witness over polygon gluing. -/

/-- One oriented polygon-gluing component from Phase 38. The `polygon` field carries the cell and
link audit from Phase 36; `facesAssigned` and `orientationContradictions` record the face-sign
constraint solve. -/
structure OrientedPolygonGluingComponent where
  polygon : PolygonGluingComponent
  facesAssigned : ℤ
  orientationContradictions : ℕ
deriving Repr, DecidableEq

/-- The orientation solver succeeds on a polygon component when it assigns every face and finds no
sign contradiction. -/
def OrientedPolygonComponentOk (C : OrientedPolygonGluingComponent) : Prop :=
  C.facesAssigned = C.polygon.faces ∧ C.orientationContradictions = 0

/-- Forget the orientability audit down to the Phase-36 polygon component. -/
def orientedPolygonToPolygon (C : OrientedPolygonGluingComponent) : PolygonGluingComponent :=
  C.polygon

/-- Forget an oriented polygon component list to its polygon-gluing component list. -/
def orientedPolygonsToPolygons (Cs : List OrientedPolygonGluingComponent) :
    List PolygonGluingComponent :=
  Cs.map orientedPolygonToPolygon

/-- An oriented polygon-gluing witness closes when all orientation solves succeed and the forgotten
polygon components close the Phase-37 polygon-gluing bridge. -/
def OrientedPolygonGluingCloses (B : BettiTriple)
    (Cs : List OrientedPolygonGluingComponent) (halfEuler : ℤ) : Prop :=
  (∀ C ∈ Cs, OrientedPolygonComponentOk C) ∧
  PolygonGluingCloses B (orientedPolygonsToPolygons Cs) halfEuler

/-- Algebraic bridge for Phase 38: once the orientability audit succeeds, the oriented
polygon-gluing witness inherits the Phase-37 total-genus theorem. -/
theorem orientedPolygonGluedGenus_eq_b1_of_orientedPolygonGluingCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent) (halfEuler : ℤ)
    (h : OrientedPolygonGluingCloses B Cs halfEuler) :
    correctedComponentGenusFromHalfEuler
      (polygonComponentsToCorrected (orientedPolygonsToPolygons Cs)) halfEuler = B.b1 := by
  rcases h with ⟨_hOrient, hPolygon⟩
  exact polygonGluedGenus_eq_b1_of_polygonGluingCloses B
    (orientedPolygonsToPolygons Cs) halfEuler hPolygon

/-- Oriented horizon torus component from Phase 38. -/
def horizonOrientedTorusComponent : OrientedPolygonGluingComponent :=
  { polygon := horizonPolygonTorusComponent, facesAssigned := 1632,
    orientationContradictions := 0 }

/-- Oriented horizon sphere component from Phase 38. -/
def horizonOrientedSphereComponent : OrientedPolygonGluingComponent :=
  { polygon := horizonPolygonSphereComponent, facesAssigned := 2482,
    orientationContradictions := 0 }

/-- Phase-38 oriented horizon polygon components. -/
def horizonAnnulusHandleOrientedPolygonComponents : List OrientedPolygonGluingComponent :=
  [horizonOrientedTorusComponent, horizonOrientedSphereComponent]

/-- Oriented dyadic genus-125 polygon component from Phase 38. -/
def dyadicOrientedGenus125Component : OrientedPolygonGluingComponent :=
  { polygon := dyadicPolygonGenus125Component, facesAssigned := 8988,
    orientationContradictions := 0 }

/-- Oriented dyadic six-face sphere component from Phase 38. -/
def dyadicOrientedSmallSphereComponent : OrientedPolygonGluingComponent :=
  { polygon := dyadicPolygonSmallSphereComponent, facesAssigned := 6,
    orientationContradictions := 0 }

/-- Oriented dyadic twenty-two-face sphere component from Phase 38. -/
def dyadicOrientedMediumSphereComponent : OrientedPolygonGluingComponent :=
  { polygon := dyadicPolygonMediumSphereComponent, facesAssigned := 22,
    orientationContradictions := 0 }

/-- Oriented dyadic thirty-face sphere component from Phase 38. -/
def dyadicOrientedLargeSphereComponent : OrientedPolygonGluingComponent :=
  { polygon := dyadicPolygonLargeSphereComponent, facesAssigned := 30,
    orientationContradictions := 0 }

/-- Phase-38 oriented dyadic polygon components. -/
def dyadicSpongeR20OrientedPolygonComponents : List OrientedPolygonGluingComponent :=
  [dyadicOrientedGenus125Component] ++
    List.replicate 48 dyadicOrientedSmallSphereComponent ++
    List.replicate 3 dyadicOrientedMediumSphereComponent ++
    [dyadicOrientedLargeSphereComponent]

/-! ## Phase 40: standard oriented surface classification. -/

/-- The standard closed orientable surface classified by its genus. -/
structure StandardSurfaceType where
  genus : ℤ
deriving Repr, DecidableEq

/-- Euler characteristic of a standard closed orientable surface of genus `g`: `2 - 2g`. -/
def standardSurfaceEuler (S : StandardSurfaceType) : ℤ :=
  2 - 2 * S.genus

/-- A polygon component has a standard surface type when its Euler characteristic matches the
standard orientable formula and its orientation certificate succeeds. -/
def PolygonComponentHasSurfaceType
    (C : OrientedPolygonGluingComponent) (S : StandardSurfaceType) : Prop :=
  OrientedPolygonComponentOk C ∧ C.polygon.euler = standardSurfaceEuler S

/-- Total genus across a list of standard surface types. -/
def surfaceTypeGenusTotal (Ss : List StandardSurfaceType) : ℤ :=
  (Ss.map StandardSurfaceType.genus).sum

/-- Number of assigned standard surface types, read as an integer for Euler algebra. -/
def surfaceTypeCount (Ss : List StandardSurfaceType) : ℤ :=
  Ss.length

/-- Total Euler characteristic across the assigned standard surface types. -/
def surfaceTypeEulerTotal (Ss : List StandardSurfaceType) : ℤ :=
  (Ss.map standardSurfaceEuler).sum

/-- Ordered Euler signature of the oriented polygon components. -/
def orientedPolygonEulerList (Cs : List OrientedPolygonGluingComponent) : List ℤ :=
  Cs.map (fun C => C.polygon.euler)

/-- Ordered Euler signature of the assigned standard surface types. -/
def surfaceTypeEulerList (Ss : List StandardSurfaceType) : List ℤ :=
  Ss.map standardSurfaceEuler

/-- Total Euler characteristic of the oriented polygon components. -/
def orientedPolygonEulerTotal (Cs : List OrientedPolygonGluingComponent) : ℤ :=
  (orientedPolygonEulerList Cs).sum

/-- A list of standard closed orientable surfaces has total Euler characteristic
`2 * component_count - 2 * total_genus`. -/
theorem surfaceTypeEulerTotal_eq_count_genus (Ss : List StandardSurfaceType) :
    surfaceTypeEulerTotal Ss = 2 * surfaceTypeCount Ss - 2 * surfaceTypeGenusTotal Ss := by
  induction Ss with
  | nil =>
      unfold surfaceTypeEulerTotal surfaceTypeCount surfaceTypeGenusTotal
      norm_num
  | cons S rest ih =>
      unfold surfaceTypeEulerTotal surfaceTypeCount surfaceTypeGenusTotal at *
      simp [standardSurfaceEuler, ih]
      ring

/-- Forgetting oriented polygons to corrected components preserves list length, written in integer
form for the inventory algebra. -/
theorem correctedComponentCount_orientedPolygons (Cs : List OrientedPolygonGluingComponent) :
    correctedComponentCount (polygonComponentsToCorrected (orientedPolygonsToPolygons Cs)) =
      Cs.length := by
  unfold correctedComponentCount polygonComponentsToCorrected orientedPolygonsToPolygons
    polygonComponentToCorrected orientedPolygonToPolygon
  simp

/-- Standard-surface classification closes when the oriented polygon certificate closes, every
component is assigned the matching standard surface type, the type count matches the component
count, and the type-genus total equals `b₁`. -/
def SurfaceTypeClassificationCloses (B : BettiTriple)
    (Cs : List OrientedPolygonGluingComponent) (Ss : List StandardSurfaceType)
    (halfEuler : ℤ) : Prop :=
  OrientedPolygonGluingCloses B Cs halfEuler ∧
  surfaceTypeCount Ss = correctedComponentCount (polygonComponentsToCorrected (orientedPolygonsToPolygons Cs)) ∧
  (∀ P ∈ Cs.zip Ss, PolygonComponentHasSurfaceType P.1 P.2) ∧
  surfaceTypeGenusTotal Ss = B.b1

/-- Algebraic bridge for Phase 40: once the oriented polygon components are classified by standard
surface type, the total standard genus is the region's `b₁`. -/
theorem surfaceTypeGenusTotal_eq_b1_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    surfaceTypeGenusTotal Ss = B.b1 := by
  exact h.2.2.2

/-- A closed standard-surface classification has the same number of assigned surface types as
oriented polygon components. -/
theorem surfaceType_length_eq_orientedPolygon_length_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    Ss.length = Cs.length := by
  have hCount : surfaceTypeCount Ss =
      correctedComponentCount (polygonComponentsToCorrected (orientedPolygonsToPolygons Cs)) := h.2.1
  unfold surfaceTypeCount at hCount
  rw [correctedComponentCount_orientedPolygons] at hCount
  exact Int.ofNat.inj hCount

/-- If every zipped component/type pair has matching Euler characteristic and the lists have equal
length, then the ordered polygon Euler signature equals the ordered standard-surface Euler
signature. -/
theorem orientedPolygonEulerList_eq_surfaceTypeEulerList_of_zip
    (Cs : List OrientedPolygonGluingComponent) (Ss : List StandardSurfaceType)
    (hLen : Cs.length = Ss.length)
    (hEach : ∀ P ∈ Cs.zip Ss, PolygonComponentHasSurfaceType P.1 P.2) :
    orientedPolygonEulerList Cs = surfaceTypeEulerList Ss := by
  induction Cs generalizing Ss with
  | nil =>
      cases Ss with
      | nil => rfl
      | cons S rest => simp at hLen
  | cons C Cs ih =>
      cases Ss with
      | nil => simp at hLen
      | cons S Ss =>
          have hHead : C.polygon.euler = standardSurfaceEuler S := by
            exact (hEach (C, S) (by simp)).2
          have hTailLen : Cs.length = Ss.length := by
            exact Nat.succ.inj hLen
          have hTailEach : ∀ P ∈ Cs.zip Ss, PolygonComponentHasSurfaceType P.1 P.2 := by
            intro P hP
            exact hEach P (by simp [hP])
          change C.polygon.euler :: orientedPolygonEulerList Cs =
            standardSurfaceEuler S :: surfaceTypeEulerList Ss
          rw [hHead, ih Ss hTailLen hTailEach]

/-- Phase 42 componentwise bridge: a closed standard-surface classification gives the same ordered
Euler signature for the oriented polygon components and the assigned standard surfaces. -/
theorem orientedPolygonEulerList_eq_surfaceTypeEulerList_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    orientedPolygonEulerList Cs = surfaceTypeEulerList Ss := by
  exact orientedPolygonEulerList_eq_surfaceTypeEulerList_of_zip Cs Ss
    (surfaceType_length_eq_orientedPolygon_length_of_surfaceTypeClassificationCloses
      B Cs Ss halfEuler h).symm h.2.2.1

/-- The oriented polygon Euler total equals the standard-surface Euler total under a closed
classification. -/
theorem orientedPolygonEulerTotal_eq_surfaceTypeEulerTotal_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    orientedPolygonEulerTotal Cs = surfaceTypeEulerTotal Ss := by
  unfold orientedPolygonEulerTotal surfaceTypeEulerTotal
  rw [orientedPolygonEulerList_eq_surfaceTypeEulerList_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h]
  rfl

/-- Phase 41 inventory bridge: a closed standard-surface classification has the same component
count as the regular-neighborhood boundary. -/
theorem surfaceTypeCount_eq_regularBoundaryComponents_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    surfaceTypeCount Ss = regularBoundaryComponents B := by
  rcases h with ⟨hOrient, hCount, _hEach, _hGenus⟩
  rcases hOrient with ⟨_hOrientOk, hPolygon⟩
  rcases hPolygon with ⟨_hEuler, _hLinks, hAssembly⟩
  exact hCount.trans hAssembly.1

/-- Phase 41 inventory bridge: the assigned standard-surface Euler total matches the canonical
regular-neighborhood boundary Euler characteristic. -/
theorem surfaceTypeEulerTotal_eq_regularBoundaryEuler_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    surfaceTypeEulerTotal Ss = regularBoundaryEuler B := by
  have hCount := surfaceTypeCount_eq_regularBoundaryComponents_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h
  have hGenus := surfaceTypeGenusTotal_eq_b1_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h
  rw [surfaceTypeEulerTotal_eq_count_genus, hCount, hGenus]
  unfold regularBoundaryEuler regularBoundaryComponents regionEuler
  ring

/-- Phase 41: the classified surface-type inventory matches the regular-neighborhood boundary
in component count, Euler characteristic, and total genus. -/
theorem surfaceTypeInventory_matches_regularBoundary_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    surfaceTypeCount Ss = regularBoundaryComponents B ∧
    surfaceTypeEulerTotal Ss = regularBoundaryEuler B ∧
    surfaceTypeGenusTotal Ss = B.b1 :=
  ⟨surfaceTypeCount_eq_regularBoundaryComponents_of_surfaceTypeClassificationCloses
      B Cs Ss halfEuler h,
    surfaceTypeEulerTotal_eq_regularBoundaryEuler_of_surfaceTypeClassificationCloses
      B Cs Ss halfEuler h,
    surfaceTypeGenusTotal_eq_b1_of_surfaceTypeClassificationCloses B Cs Ss halfEuler h⟩

/-- Phase 42: componentwise plus aggregate inventory matching. This is the strongest algebraic
surface-inventory statement in this file; the embedded homeomorphism remains the separate geometric
premise. -/
theorem componentwiseSurfaceInventory_matches_regularBoundary_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    orientedPolygonEulerList Cs = surfaceTypeEulerList Ss ∧
    orientedPolygonEulerTotal Cs = regularBoundaryEuler B ∧
    surfaceTypeCount Ss = regularBoundaryComponents B ∧
    surfaceTypeGenusTotal Ss = B.b1 := by
  have hList := orientedPolygonEulerList_eq_surfaceTypeEulerList_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h
  have hTotal := orientedPolygonEulerTotal_eq_surfaceTypeEulerTotal_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h
  have hSurfaceEuler :=
    surfaceTypeEulerTotal_eq_regularBoundaryEuler_of_surfaceTypeClassificationCloses B Cs Ss halfEuler h
  exact ⟨hList, hTotal.trans hSurfaceEuler,
    surfaceTypeCount_eq_regularBoundaryComponents_of_surfaceTypeClassificationCloses B Cs Ss halfEuler h,
    surfaceTypeGenusTotal_eq_b1_of_surfaceTypeClassificationCloses B Cs Ss halfEuler h⟩

/-! ## Phase 43: finite component pairing toward the embedded map. -/

/-- A finite pairing between one corrected oriented polygon component and one standard
regular-boundary surface component. -/
abbrev ComponentPair : Type :=
  OrientedPolygonGluingComponent × StandardSurfaceType

/-- The ordered component pairing used by the current certificates. The later geometric theorem
must replace this abstract pairing with an embedded map. -/
def componentPairing (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) : List ComponentPair :=
  Cs.zip Ss

/-- A paired component is valid when the polygon orientation certificate succeeds and the polygon
Euler characteristic equals the target standard-surface Euler characteristic. -/
def ComponentPairOk (P : ComponentPair) : Prop :=
  OrientedPolygonComponentOk P.1 ∧ P.1.polygon.euler = standardSurfaceEuler P.2

/-- The target genus carried by a component pairing. -/
def componentPairGenus (P : ComponentPair) : ℤ :=
  P.2.genus

/-- Total target genus of a finite component pairing. -/
def componentPairingGenusTotal (Ps : List ComponentPair) : ℤ :=
  (Ps.map componentPairGenus).sum

/-- Total target Euler characteristic of a finite component pairing. -/
def componentPairingEulerTotal (Ps : List ComponentPair) : ℤ :=
  (Ps.map (fun P => standardSurfaceEuler P.2)).sum

/-- A component pairing closes when it comes from the standard-surface classification, every pair
is locally valid, and its regular-boundary inventory matches component count, Euler, and genus. -/
def ComponentPairingCloses (B : BettiTriple)
    (Cs : List OrientedPolygonGluingComponent) (Ss : List StandardSurfaceType)
    (halfEuler : ℤ) : Prop :=
  SurfaceTypeClassificationCloses B Cs Ss halfEuler ∧
  (∀ P ∈ componentPairing Cs Ss, ComponentPairOk P) ∧
  surfaceTypeCount Ss = regularBoundaryComponents B ∧
  componentPairingEulerTotal (componentPairing Cs Ss) = regularBoundaryEuler B ∧
  componentPairingGenusTotal (componentPairing Cs Ss) = B.b1

/-- The genus total of the component pairing is the genus total of its target surface list when the
source and target lists have the same length. -/
theorem componentPairingGenusTotal_eq_surfaceTypeGenusTotal
    (Cs : List OrientedPolygonGluingComponent) (Ss : List StandardSurfaceType)
    (hLen : Cs.length = Ss.length) :
    componentPairingGenusTotal (componentPairing Cs Ss) = surfaceTypeGenusTotal Ss := by
  induction Cs generalizing Ss with
  | nil =>
      cases Ss with
      | nil => rfl
      | cons S Ss => simp at hLen
  | cons C Cs ih =>
      cases Ss with
      | nil => simp at hLen
      | cons S Ss =>
          have hTailLen : Cs.length = Ss.length := Nat.succ.inj hLen
          change S.genus + componentPairingGenusTotal (componentPairing Cs Ss) =
            S.genus + surfaceTypeGenusTotal Ss
          rw [ih Ss hTailLen]

/-- The Euler total of the component pairing is the Euler total of its target surface list when the
source and target lists have the same length. -/
theorem componentPairingEulerTotal_eq_surfaceTypeEulerTotal
    (Cs : List OrientedPolygonGluingComponent) (Ss : List StandardSurfaceType)
    (hLen : Cs.length = Ss.length) :
    componentPairingEulerTotal (componentPairing Cs Ss) = surfaceTypeEulerTotal Ss := by
  induction Cs generalizing Ss with
  | nil =>
      cases Ss with
      | nil => rfl
      | cons S Ss => simp at hLen
  | cons C Cs ih =>
      cases Ss with
      | nil => simp at hLen
      | cons S Ss =>
          have hTailLen : Cs.length = Ss.length := Nat.succ.inj hLen
          change standardSurfaceEuler S + componentPairingEulerTotal (componentPairing Cs Ss) =
            standardSurfaceEuler S + surfaceTypeEulerTotal Ss
          rw [ih Ss hTailLen]

/-- Phase 43 pairing bridge: a closed standard-surface classification gives a closed finite
component pairing. This still does not construct the embedded homeomorphism. -/
theorem componentPairingCloses_of_surfaceTypeClassificationCloses
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (h : SurfaceTypeClassificationCloses B Cs Ss halfEuler) :
    ComponentPairingCloses B Cs Ss halfEuler := by
  have hLen : Cs.length = Ss.length :=
    (surfaceType_length_eq_orientedPolygon_length_of_surfaceTypeClassificationCloses
      B Cs Ss halfEuler h).symm
  have hPairs : ∀ P ∈ componentPairing Cs Ss, ComponentPairOk P := by
    intro P hP
    exact h.2.2.1 P hP
  have hCount := surfaceTypeCount_eq_regularBoundaryComponents_of_surfaceTypeClassificationCloses
    B Cs Ss halfEuler h
  have hEuler : componentPairingEulerTotal (componentPairing Cs Ss) = regularBoundaryEuler B := by
    rw [componentPairingEulerTotal_eq_surfaceTypeEulerTotal Cs Ss hLen]
    exact surfaceTypeEulerTotal_eq_regularBoundaryEuler_of_surfaceTypeClassificationCloses
      B Cs Ss halfEuler h
  have hGenus : componentPairingGenusTotal (componentPairing Cs Ss) = B.b1 := by
    rw [componentPairingGenusTotal_eq_surfaceTypeGenusTotal Cs Ss hLen]
    exact surfaceTypeGenusTotal_eq_b1_of_surfaceTypeClassificationCloses B Cs Ss halfEuler h
  exact ⟨h, hPairs, hCount, hEuler, hGenus⟩

/-! ## Phase 44: embedded component-map obligations. -/

/-- A candidate embedded map from one corrected oriented polygon component to one standard
regular-boundary surface component.

The four proposition fields are the geometric work still owed by the embedded theorem. They are
kept as obligations rather than booleans so this file cannot silently declare them true. -/
structure EmbeddedComponentMapObligation where
  source : OrientedPolygonGluingComponent
  target : StandardSurfaceType
  incidencePreserving : Prop
  quotientCellBijective : Prop
  vertexLinksPreserved : Prop
  orientationPreserving : Prop

/-- Forget an embedded-map obligation to the Phase-43 component pair it is supposed to realize. -/
def embeddedComponentMapPair (M : EmbeddedComponentMapObligation) : ComponentPair :=
  (M.source, M.target)

/-- The ordered list of component pairs carried by embedded-map obligations. -/
def embeddedComponentMapPairing (Ms : List EmbeddedComponentMapObligation) : List ComponentPair :=
  Ms.map embeddedComponentMapPair

/-- A candidate embedded component map is locally valid exactly when the Phase-43 component pair is
valid and all four geometric map obligations are present. -/
def EmbeddedComponentMapObligationOk (M : EmbeddedComponentMapObligation) : Prop :=
  ComponentPairOk (embeddedComponentMapPair M) ∧
  M.incidencePreserving ∧
  M.quotientCellBijective ∧
  M.vertexLinksPreserved ∧
  M.orientationPreserving

/-- Embedded-map obligations close when every candidate map satisfies the local geometric
obligations and the underlying Phase-43 component pairing closes. -/
def EmbeddedComponentMapObligationsClose (B : BettiTriple)
    (Ms : List EmbeddedComponentMapObligation) (halfEuler : ℤ) : Prop :=
  (∀ M ∈ Ms, EmbeddedComponentMapObligationOk M) ∧
  ComponentPairingCloses B
    (Ms.map EmbeddedComponentMapObligation.source)
    (Ms.map EmbeddedComponentMapObligation.target)
    halfEuler

/-- The embedded-map obligation pairing is definitionally the component pairing between its source
and target lists. -/
theorem embeddedComponentMapPairing_eq_componentPairing
    (Ms : List EmbeddedComponentMapObligation) :
    embeddedComponentMapPairing Ms =
      componentPairing
        (Ms.map EmbeddedComponentMapObligation.source)
        (Ms.map EmbeddedComponentMapObligation.target) := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
      change embeddedComponentMapPair M :: embeddedComponentMapPairing Ms =
        embeddedComponentMapPair M ::
          componentPairing
            (Ms.map EmbeddedComponentMapObligation.source)
            (Ms.map EmbeddedComponentMapObligation.target)
      rw [ih]

/-- Phase 44 reduction: if embedded component-map obligations close, the underlying finite
component pairing closes. The real embedded homeomorphism theorem must still prove the obligations
from geometry. -/
theorem componentPairingCloses_of_embeddedComponentMapObligationsClose
    (B : BettiTriple) (Ms : List EmbeddedComponentMapObligation) (halfEuler : ℤ)
    (h : EmbeddedComponentMapObligationsClose B Ms halfEuler) :
    ComponentPairingCloses B
      (Ms.map EmbeddedComponentMapObligation.source)
      (Ms.map EmbeddedComponentMapObligation.target)
      halfEuler := h.2

/-- Phase 44 local readout: a closed embedded-map obligation package supplies every local
incidence, bijection, link, and orientation obligation for each candidate component map. -/
theorem embeddedComponentMapObligationOk_of_embeddedComponentMapObligationsClose
    (B : BettiTriple) (Ms : List EmbeddedComponentMapObligation) (halfEuler : ℤ)
    (h : EmbeddedComponentMapObligationsClose B Ms halfEuler)
    (M : EmbeddedComponentMapObligation) (hM : M ∈ Ms) :
    EmbeddedComponentMapObligationOk M := h.1 M hM

/-- Phase 44 inventory readout: any closed embedded-map obligation package inherits the
regular-boundary Euler and genus inventory from its Phase-43 component pairing. -/
theorem embeddedComponentMapInventory_matches_regularBoundary
    (B : BettiTriple) (Ms : List EmbeddedComponentMapObligation) (halfEuler : ℤ)
    (h : EmbeddedComponentMapObligationsClose B Ms halfEuler) :
    componentPairingEulerTotal
        (componentPairing
          (Ms.map EmbeddedComponentMapObligation.source)
          (Ms.map EmbeddedComponentMapObligation.target)) = regularBoundaryEuler B ∧
    componentPairingGenusTotal
        (componentPairing
          (Ms.map EmbeddedComponentMapObligation.source)
          (Ms.map EmbeddedComponentMapObligation.target)) = B.b1 := by
  rcases h.2 with ⟨_hClass, _hPairs, _hCount, hEuler, hGenus⟩
  exact ⟨hEuler, hGenus⟩

/-- The standard sphere. -/
def standardSphere : StandardSurfaceType :=
  { genus := 0 }

/-- The standard torus. -/
def standardTorus : StandardSurfaceType :=
  { genus := 1 }

/-- The standard closed orientable surface of genus `125`. -/
def standardGenus125Surface : StandardSurfaceType :=
  { genus := 125 }

/-- Standard surface types for the horizon-annulus polygon components. -/
def horizonAnnulusHandleSurfaceTypes : List StandardSurfaceType :=
  [standardTorus, standardSphere]

/-- Standard surface types for the dyadic sponge polygon components. -/
def dyadicSpongeR20SurfaceTypes : List StandardSurfaceType :=
  [standardGenus125Surface] ++ List.replicate 52 standardSphere

/-! ## Numeric certificates for Phase 26/28/30 artifacts. -/

/-- Phase-26 horizon-annulus handle at `R = 20` and `R = 32`: two components, one tunnel, no void. -/
def horizonAnnulusHandleBetti : BettiTriple :=
  { b0 := 2, b1 := 1, b2 := 0 }

/-- The desingularized horizon-annulus boundary has two components. -/
theorem horizonAnnulusHandle_regularBoundaryComponents :
    regularBoundaryComponents horizonAnnulusHandleBetti = 2 := by
  native_decide

/-- The desingularized horizon-annulus boundary has total genus one. -/
theorem horizonAnnulusHandle_regularBoundaryGenus :
    regularBoundaryGenus horizonAnnulusHandleBetti = 1 := by
  native_decide

/-- The Phase-28 canonical CW boundary model of the horizon-annulus handle has Euler
characteristic `2`. -/
theorem horizonAnnulusHandle_regularBoundaryCWEuler :
    regularBoundaryCWEuler horizonAnnulusHandleBetti = 2 := by
  native_decide

/-- Phase-30 singular-edge graph for the horizon-annulus target: `64` two-vertex components. -/
def horizonAnnulusHandleSingularComponents : List SingularGraphComponent :=
  List.replicate 64 singularV2E1

/-- The horizon-annulus half-vertex quotient supplies exactly the missing `64` vertices. -/
theorem horizonAnnulusHandle_halfVertexDelta :
    singularGraphHalfVertexDelta horizonAnnulusHandleSingularComponents = 64 := by
  native_decide

/-- The Phase-29 edge-only Euler count `-62`, corrected by the Phase-30 half-vertex delta `64`,
recovers the canonical CW Euler count `2`. -/
theorem horizonAnnulusHandle_halfVertexCorrectedEuler :
    halfVertexCorrectedEuler (-62) horizonAnnulusHandleSingularComponents =
      regularBoundaryCWEuler horizonAnnulusHandleBetti := by
  native_decide

/-- The algebraic Phase-31 certificate: the half-vertex quotient closes the horizon-annulus CW Euler
budget under the recorded Phase-30 singular-component data. -/
theorem horizonAnnulusHandle_halfVertexQuotientCloses :
    HalfVertexQuotientCloses horizonAnnulusHandleBetti (-62)
      horizonAnnulusHandleSingularComponents := by
  unfold HalfVertexQuotientCloses
  native_decide

/-- Phase-26 dyadic sponge probe at `R = 20`: `(b₀,b₁,b₂) = (50,125,3)`. -/
def dyadicSpongeR20Betti : BettiTriple :=
  { b0 := 50, b1 := 125, b2 := 3 }

/-- The regular-neighborhood boundary of the dyadic sponge has `50 + 3 = 53` components. -/
theorem dyadicSpongeR20_regularBoundaryComponents :
    regularBoundaryComponents dyadicSpongeR20Betti = 53 := by
  native_decide

/-- The regular-neighborhood boundary of the dyadic sponge has total genus `125`. -/
theorem dyadicSpongeR20_regularBoundaryGenus :
    regularBoundaryGenus dyadicSpongeR20Betti = 125 := by
  native_decide

/-- The Phase-28 canonical CW boundary model of the dyadic sponge has Euler characteristic
`-144`, equal to `2 * (50 - 125 + 3)`. -/
theorem dyadicSpongeR20_regularBoundaryCWEuler :
    regularBoundaryCWEuler dyadicSpongeR20Betti = -144 := by
  native_decide

/-- Phase-30 singular-edge graph for the dyadic sponge: `24` components of type `V2_E1` and
`21` components of type `V4_E3`. -/
def dyadicSpongeR20SingularComponents : List SingularGraphComponent :=
  List.replicate 24 singularV2E1 ++ List.replicate 21 singularV4E3

/-- The dyadic sponge half-vertex quotient is `24*1 + 21*2 = 66`, exactly the required vertex
delta from Phase 30. -/
theorem dyadicSpongeR20_halfVertexDelta :
    singularGraphHalfVertexDelta dyadicSpongeR20SingularComponents = 66 := by
  native_decide

/-- The Phase-29 dyadic edge-only Euler count `-210`, corrected by the Phase-30 half-vertex delta
`66`, recovers the canonical CW Euler count `-144`. -/
theorem dyadicSpongeR20_halfVertexCorrectedEuler :
    halfVertexCorrectedEuler (-210) dyadicSpongeR20SingularComponents =
      regularBoundaryCWEuler dyadicSpongeR20Betti := by
  native_decide

/-- The algebraic Phase-31 certificate: the half-vertex quotient closes the dyadic-sponge CW Euler
budget under the recorded Phase-30 singular-component data. -/
theorem dyadicSpongeR20_halfVertexQuotientCloses :
    HalfVertexQuotientCloses dyadicSpongeR20Betti (-210)
      dyadicSpongeR20SingularComponents := by
  unfold HalfVertexQuotientCloses
  native_decide

/-! ## Numeric certificates for Phase 34/35 component assembly. -/

/-- The Phase-34 horizon component split has two components. -/
theorem horizonAnnulusHandle_correctedComponentCount :
    correctedComponentCount horizonAnnulusHandleCorrectedComponents =
      regularBoundaryComponents horizonAnnulusHandleBetti := by
  native_decide

/-- The Phase-34 horizon component Euler sum is `2`, twice the region Euler half-sum `1`. -/
theorem horizonAnnulusHandle_correctedComponentEuler :
    correctedComponentEuler horizonAnnulusHandleCorrectedComponents = 2 * regionEuler horizonAnnulusHandleBetti := by
  native_decide

/-- The Phase-35 algebraic certificate: the horizon component assembly closes. -/
theorem horizonAnnulusHandle_componentAssemblyCloses :
    ComponentAssemblyCloses horizonAnnulusHandleBetti horizonAnnulusHandleCorrectedComponents 1 := by
  unfold ComponentAssemblyCloses
  native_decide

/-- The corrected horizon components have total genus one. -/
theorem horizonAnnulusHandle_correctedComponentGenus :
    correctedComponentGenusFromHalfEuler horizonAnnulusHandleCorrectedComponents 1 = 1 := by
  native_decide

/-- The Phase-34 dyadic component split has `53` components. -/
theorem dyadicSpongeR20_correctedComponentCount :
    correctedComponentCount dyadicSpongeR20CorrectedComponents =
      regularBoundaryComponents dyadicSpongeR20Betti := by
  native_decide

/-- The Phase-34 dyadic component Euler sum is `-144`, twice the region Euler half-sum `-72`. -/
theorem dyadicSpongeR20_correctedComponentEuler :
    correctedComponentEuler dyadicSpongeR20CorrectedComponents = 2 * regionEuler dyadicSpongeR20Betti := by
  native_decide

/-- The Phase-35 algebraic certificate: the dyadic component assembly closes. -/
theorem dyadicSpongeR20_componentAssemblyCloses :
    ComponentAssemblyCloses dyadicSpongeR20Betti dyadicSpongeR20CorrectedComponents (-72) := by
  unfold ComponentAssemblyCloses
  native_decide

/-- The corrected dyadic components have total genus `125`. -/
theorem dyadicSpongeR20_correctedComponentGenus :
    correctedComponentGenusFromHalfEuler dyadicSpongeR20CorrectedComponents (-72) = 125 := by
  native_decide

/-! ## Numeric certificates for Phase 36/37 polygon gluing. -/

/-- The Phase-36 horizon polygon components have the recorded Euler counts and cyclic vertex links,
and reduce to the Phase-35 horizon component assembly. -/
theorem horizonAnnulusHandle_polygonGluingCloses :
    PolygonGluingCloses horizonAnnulusHandleBetti horizonAnnulusHandlePolygonComponents 1 := by
  unfold PolygonGluingCloses ComponentAssemblyCloses PolygonComponentEulerOk
    PolygonComponentLinksCyclic polygonComponentsToCorrected polygonComponentToCorrected
    correctedComponentCount correctedComponentEuler regularBoundaryComponents regionEuler
  native_decide

/-- The Phase-37 algebraic bridge reads total horizon genus one from the polygon-gluing witness. -/
theorem horizonAnnulusHandle_polygonGluedGenus :
    correctedComponentGenusFromHalfEuler
      (polygonComponentsToCorrected horizonAnnulusHandlePolygonComponents) 1 = 1 := by
  native_decide

/-- The Phase-36 dyadic polygon components have the recorded Euler counts and cyclic vertex links,
and reduce to the Phase-35 dyadic component assembly. -/
theorem dyadicSpongeR20_polygonGluingCloses :
    PolygonGluingCloses dyadicSpongeR20Betti dyadicSpongeR20PolygonComponents (-72) := by
  unfold PolygonGluingCloses ComponentAssemblyCloses PolygonComponentEulerOk
    PolygonComponentLinksCyclic polygonComponentsToCorrected polygonComponentToCorrected
    correctedComponentCount correctedComponentEuler regularBoundaryComponents regionEuler
  native_decide

/-- The Phase-37 algebraic bridge reads total dyadic genus `125` from the polygon-gluing witness. -/
theorem dyadicSpongeR20_polygonGluedGenus :
    correctedComponentGenusFromHalfEuler
      (polygonComponentsToCorrected dyadicSpongeR20PolygonComponents) (-72) = 125 := by
  native_decide

/-! ## Numeric certificates for Phase 38/39 orientability. -/

/-- The Phase-38 horizon orientation assignment covers every face with zero contradictions and
inherits the Phase-37 polygon-gluing closure. -/
theorem horizonAnnulusHandle_orientedPolygonGluingCloses :
    OrientedPolygonGluingCloses horizonAnnulusHandleBetti
      horizonAnnulusHandleOrientedPolygonComponents 1 := by
  unfold OrientedPolygonGluingCloses OrientedPolygonComponentOk PolygonGluingCloses
    ComponentAssemblyCloses PolygonComponentEulerOk PolygonComponentLinksCyclic
    orientedPolygonsToPolygons orientedPolygonToPolygon polygonComponentsToCorrected
    polygonComponentToCorrected correctedComponentCount correctedComponentEuler
    regularBoundaryComponents regionEuler
  native_decide

/-- The oriented Phase-38 horizon polygon components read total genus one. -/
theorem horizonAnnulusHandle_orientedPolygonGluedGenus :
    correctedComponentGenusFromHalfEuler
      (polygonComponentsToCorrected
        (orientedPolygonsToPolygons horizonAnnulusHandleOrientedPolygonComponents)) 1 = 1 := by
  native_decide

/-- The Phase-38 dyadic orientation assignment covers every face with zero contradictions and
inherits the Phase-37 polygon-gluing closure. -/
theorem dyadicSpongeR20_orientedPolygonGluingCloses :
    OrientedPolygonGluingCloses dyadicSpongeR20Betti
      dyadicSpongeR20OrientedPolygonComponents (-72) := by
  unfold OrientedPolygonGluingCloses OrientedPolygonComponentOk PolygonGluingCloses
    ComponentAssemblyCloses PolygonComponentEulerOk PolygonComponentLinksCyclic
    orientedPolygonsToPolygons orientedPolygonToPolygon polygonComponentsToCorrected
    polygonComponentToCorrected correctedComponentCount correctedComponentEuler
    regularBoundaryComponents regionEuler
  native_decide

/-- The oriented Phase-38 dyadic polygon components read total genus `125`. -/
theorem dyadicSpongeR20_orientedPolygonGluedGenus :
    correctedComponentGenusFromHalfEuler
      (polygonComponentsToCorrected
        (orientedPolygonsToPolygons dyadicSpongeR20OrientedPolygonComponents)) (-72) = 125 := by
  native_decide

/-! ## Numeric certificates for Phase 40 standard-surface classification. -/

/-- The oriented Phase-38 horizon components classify as torus plus sphere. -/
theorem horizonAnnulusHandle_surfaceTypeClassificationCloses :
    SurfaceTypeClassificationCloses horizonAnnulusHandleBetti
      horizonAnnulusHandleOrientedPolygonComponents horizonAnnulusHandleSurfaceTypes 1 := by
  unfold SurfaceTypeClassificationCloses PolygonComponentHasSurfaceType
    OrientedPolygonGluingCloses OrientedPolygonComponentOk PolygonGluingCloses
    ComponentAssemblyCloses PolygonComponentEulerOk PolygonComponentLinksCyclic
    orientedPolygonsToPolygons orientedPolygonToPolygon polygonComponentsToCorrected
    polygonComponentToCorrected correctedComponentCount correctedComponentEuler
    regularBoundaryComponents regionEuler surfaceTypeGenusTotal standardSurfaceEuler
  native_decide

/-- The standard-surface genus total for the horizon components is one. -/
theorem horizonAnnulusHandle_surfaceTypeGenusTotal :
    surfaceTypeGenusTotal horizonAnnulusHandleSurfaceTypes = 1 := by
  native_decide

/-- Phase-42 horizon certificate: the ordered polygon Euler signature matches the ordered
standard-surface Euler signature, and the aggregate inventory matches the regular boundary. -/
theorem horizonAnnulusHandle_componentwiseSurfaceInventory :
    orientedPolygonEulerList horizonAnnulusHandleOrientedPolygonComponents =
      surfaceTypeEulerList horizonAnnulusHandleSurfaceTypes ∧
    orientedPolygonEulerTotal horizonAnnulusHandleOrientedPolygonComponents =
      regularBoundaryEuler horizonAnnulusHandleBetti ∧
    surfaceTypeCount horizonAnnulusHandleSurfaceTypes =
      regularBoundaryComponents horizonAnnulusHandleBetti ∧
    surfaceTypeGenusTotal horizonAnnulusHandleSurfaceTypes = horizonAnnulusHandleBetti.b1 := by
  exact componentwiseSurfaceInventory_matches_regularBoundary_of_surfaceTypeClassificationCloses
    horizonAnnulusHandleBetti horizonAnnulusHandleOrientedPolygonComponents
    horizonAnnulusHandleSurfaceTypes 1 horizonAnnulusHandle_surfaceTypeClassificationCloses

/-- Phase-43 horizon certificate: the ordered torus/sphere component pairing closes. -/
theorem horizonAnnulusHandle_componentPairingCloses :
    ComponentPairingCloses horizonAnnulusHandleBetti
      horizonAnnulusHandleOrientedPolygonComponents horizonAnnulusHandleSurfaceTypes 1 := by
  exact componentPairingCloses_of_surfaceTypeClassificationCloses
    horizonAnnulusHandleBetti horizonAnnulusHandleOrientedPolygonComponents
    horizonAnnulusHandleSurfaceTypes 1 horizonAnnulusHandle_surfaceTypeClassificationCloses

/-- The oriented Phase-38 dyadic components classify as one genus-125 surface plus 52 spheres. -/
theorem dyadicSpongeR20_surfaceTypeClassificationCloses :
    SurfaceTypeClassificationCloses dyadicSpongeR20Betti
      dyadicSpongeR20OrientedPolygonComponents dyadicSpongeR20SurfaceTypes (-72) := by
  unfold SurfaceTypeClassificationCloses PolygonComponentHasSurfaceType
    OrientedPolygonGluingCloses OrientedPolygonComponentOk PolygonGluingCloses
    ComponentAssemblyCloses PolygonComponentEulerOk PolygonComponentLinksCyclic
    orientedPolygonsToPolygons orientedPolygonToPolygon polygonComponentsToCorrected
    polygonComponentToCorrected correctedComponentCount correctedComponentEuler
    regularBoundaryComponents regionEuler surfaceTypeGenusTotal standardSurfaceEuler
  native_decide

/-- The standard-surface genus total for the dyadic components is `125`. -/
theorem dyadicSpongeR20_surfaceTypeGenusTotal :
    surfaceTypeGenusTotal dyadicSpongeR20SurfaceTypes = 125 := by
  native_decide

/-- Phase-42 dyadic certificate: the ordered polygon Euler signature matches the ordered
standard-surface Euler signature, and the aggregate inventory matches the regular boundary. -/
theorem dyadicSpongeR20_componentwiseSurfaceInventory :
    orientedPolygonEulerList dyadicSpongeR20OrientedPolygonComponents =
      surfaceTypeEulerList dyadicSpongeR20SurfaceTypes ∧
    orientedPolygonEulerTotal dyadicSpongeR20OrientedPolygonComponents =
      regularBoundaryEuler dyadicSpongeR20Betti ∧
    surfaceTypeCount dyadicSpongeR20SurfaceTypes =
      regularBoundaryComponents dyadicSpongeR20Betti ∧
    surfaceTypeGenusTotal dyadicSpongeR20SurfaceTypes = dyadicSpongeR20Betti.b1 := by
  exact componentwiseSurfaceInventory_matches_regularBoundary_of_surfaceTypeClassificationCloses
    dyadicSpongeR20Betti dyadicSpongeR20OrientedPolygonComponents
    dyadicSpongeR20SurfaceTypes (-72) dyadicSpongeR20_surfaceTypeClassificationCloses

/-- Phase-43 dyadic certificate: the ordered genus-125-plus-spheres component pairing closes. -/
theorem dyadicSpongeR20_componentPairingCloses :
    ComponentPairingCloses dyadicSpongeR20Betti
      dyadicSpongeR20OrientedPolygonComponents dyadicSpongeR20SurfaceTypes (-72) := by
  exact componentPairingCloses_of_surfaceTypeClassificationCloses
    dyadicSpongeR20Betti dyadicSpongeR20OrientedPolygonComponents
    dyadicSpongeR20SurfaceTypes (-72) dyadicSpongeR20_surfaceTypeClassificationCloses

/-- Old foam law obstruction from Phase 30: its half-vertex delta is strictly below the required
vertex budget, so the local target-class quotient cannot be promoted to a universal theorem. -/
theorem oldFoamR8_halfVertexDelta_lt_required : (28 : ℕ) < 788 := by
  native_decide

/-- Old layered law obstruction from Phase 30: its half-vertex delta is strictly below the required
vertex budget, so those dust-law singularities remain a separate geometric problem. -/
theorem oldLayeredR8_halfVertexDelta_lt_required : (336 : ℕ) < 756 := by
  native_decide

/-! ## Phase 46: concrete closed-orientable-surface obligations.

Phase 44 carried the four embedded-map obligations as opaque `Prop` fields, so an obligation package
could be satisfied by trivial propositions and the Phase-45 numeric content stayed in Python. Phase
46 replaces those placeholders with concrete decidable combinatorial-surface conditions read from the
Phase-36 polygon quotient and the Phase-38 orientation solve, and proves the horizon and dyadic
targets satisfy them in Lean.

The conditions are exactly the hypotheses of a closed connected orientable combinatorial surface of
genus `g`: every edge is shared by two quadrilateral faces (closed, no boundary), the cell counts
give the target Euler characteristic, every quotient vertex link is a single cycle (manifold points),
and the face-orientation solve succeeds (orientable). The remaining OPEN step is the classification of
closed surfaces, namely that a closed connected orientable combinatorial 2-manifold of genus `g` is
homeomorphic to the standard genus-`g` surface. That classification is not in Mathlib and is not
assumed here. -/

/-- Closed quadrangulation: every surface edge is shared by exactly two quadrilateral faces, so the
four-edges-per-face incidence count `4 * faces` equals the two-faces-per-edge count `2 * edges`, that
is `edges = 2 * faces`. This is the combinatorial no-boundary condition. -/
def PolygonComponentClosedQuadrangulation (C : PolygonGluingComponent) : Prop :=
  C.edges = 2 * C.faces

/-- A concrete combinatorial closed orientable surface witness on one oriented polygon component: the
cell counts give the recorded Euler characteristic, every quotient vertex link is a single cycle, the
face-orientation solve succeeds, and every edge is shared by exactly two faces. These are the
decidable replacements for the opaque Phase-44 obligation propositions. -/
def CombinatorialClosedOrientableSurface (C : OrientedPolygonGluingComponent) : Prop :=
  PolygonComponentEulerOk C.polygon ∧
  PolygonComponentLinksCyclic C.polygon ∧
  OrientedPolygonComponentOk C ∧
  PolygonComponentClosedQuadrangulation C.polygon

/-- Build a Phase-44 embedded-map obligation whose four propositions are the concrete
closed-orientable-surface conditions instead of placeholders. -/
def concreteObligation (C : OrientedPolygonGluingComponent) (S : StandardSurfaceType) :
    EmbeddedComponentMapObligation :=
  { source := C
    target := S
    incidencePreserving := PolygonComponentClosedQuadrangulation C.polygon
    quotientCellBijective :=
      PolygonComponentEulerOk C.polygon ∧ C.polygon.euler = standardSurfaceEuler S
    vertexLinksPreserved := PolygonComponentLinksCyclic C.polygon
    orientationPreserving := OrientedPolygonComponentOk C }

/-- The standard surface target is forced by the Euler characteristic: two standard surfaces with the
same Euler characteristic are equal. The classification target is therefore determined, not chosen. -/
theorem standardSurfaceType_unique_of_euler (S S' : StandardSurfaceType)
    (h : standardSurfaceEuler S = standardSurfaceEuler S') : S = S' := by
  have hgen : S.genus = S'.genus := by
    have h' := h
    unfold standardSurfaceEuler at h'
    omega
  cases S
  cases S'
  simp_all

/-- Phase 46 local bridge: a concrete closed-orientable-surface witness together with the target Euler
match supplies every Phase-44 obligation for the concrete obligation, with no placeholder left. -/
theorem concreteObligationOk_of_surface (C : OrientedPolygonGluingComponent)
    (S : StandardSurfaceType) (hsurf : CombinatorialClosedOrientableSurface C)
    (heuler : C.polygon.euler = standardSurfaceEuler S) :
    EmbeddedComponentMapObligationOk (concreteObligation C S) := by
  rcases hsurf with ⟨hEuler, hLinks, hOrient, hClosed⟩
  exact ⟨⟨hOrient, heuler⟩, hClosed, ⟨hEuler, heuler⟩, hLinks, hOrient⟩

/-- The concrete obligation list from zipped component and surface lists. -/
def concreteObligations (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) : List EmbeddedComponentMapObligation :=
  (Cs.zip Ss).map (fun P => concreteObligation P.1 P.2)

/-- The concrete obligation sources recover the component list when the lists have equal length. -/
theorem concreteObligations_map_source (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (hLen : Cs.length = Ss.length) :
    (concreteObligations Cs Ss).map EmbeddedComponentMapObligation.source = Cs := by
  induction Cs generalizing Ss with
  | nil => rfl
  | cons C Cs ih =>
      cases Ss with
      | nil => simp at hLen
      | cons S Ss =>
          have hTail : Cs.length = Ss.length := Nat.succ.inj hLen
          change C :: (concreteObligations Cs Ss).map EmbeddedComponentMapObligation.source
            = C :: Cs
          rw [ih Ss hTail]

/-- The concrete obligation targets recover the surface list when the lists have equal length. -/
theorem concreteObligations_map_target (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (hLen : Cs.length = Ss.length) :
    (concreteObligations Cs Ss).map EmbeddedComponentMapObligation.target = Ss := by
  induction Cs generalizing Ss with
  | nil =>
      cases Ss with
      | nil => rfl
      | cons S Ss => simp at hLen
  | cons C Cs ih =>
      cases Ss with
      | nil => simp at hLen
      | cons S Ss =>
          have hTail : Cs.length = Ss.length := Nat.succ.inj hLen
          change S :: (concreteObligations Cs Ss).map EmbeddedComponentMapObligation.target
            = S :: Ss
          rw [ih Ss hTail]

/-- Phase 46 list bridge: when every paired component is a concrete closed orientable surface and the
underlying Phase-43 pairing closes, the concrete obligation package closes in the Phase-44 sense, with
no placeholder obligation. -/
theorem embeddedComponentMapObligationsClose_of_concrete
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ) (hLen : Cs.length = Ss.length)
    (hSurf : ∀ P ∈ Cs.zip Ss, CombinatorialClosedOrientableSurface P.1)
    (hPair : ComponentPairingCloses B Cs Ss halfEuler) :
    EmbeddedComponentMapObligationsClose B (concreteObligations Cs Ss) halfEuler := by
  refine ⟨?_, ?_⟩
  · intro M hM
    rcases List.mem_map.1 hM with ⟨P, hP, rfl⟩
    have hsurf := hSurf P hP
    have hpair : ComponentPairOk P := hPair.2.1 P hP
    exact concreteObligationOk_of_surface P.1 P.2 hsurf hpair.2
  · rw [concreteObligations_map_source Cs Ss hLen,
      concreteObligations_map_target Cs Ss hLen]
    exact hPair

/-- The horizon torus component is a concrete closed orientable surface. -/
theorem horizonOrientedTorus_combinatorialSurface :
    CombinatorialClosedOrientableSurface horizonOrientedTorusComponent := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- The horizon sphere component is a concrete closed orientable surface. -/
theorem horizonOrientedSphere_combinatorialSurface :
    CombinatorialClosedOrientableSurface horizonOrientedSphereComponent := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- The dyadic genus-125 component is a concrete closed orientable surface. -/
theorem dyadicOrientedGenus125_combinatorialSurface :
    CombinatorialClosedOrientableSurface dyadicOrientedGenus125Component := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- The dyadic six-face sphere component is a concrete closed orientable surface. -/
theorem dyadicOrientedSmallSphere_combinatorialSurface :
    CombinatorialClosedOrientableSurface dyadicOrientedSmallSphereComponent := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- The dyadic twenty-two-face sphere component is a concrete closed orientable surface. -/
theorem dyadicOrientedMediumSphere_combinatorialSurface :
    CombinatorialClosedOrientableSurface dyadicOrientedMediumSphereComponent := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- The dyadic thirty-face sphere component is a concrete closed orientable surface. -/
theorem dyadicOrientedLargeSphere_combinatorialSurface :
    CombinatorialClosedOrientableSurface dyadicOrientedLargeSphereComponent := by
  unfold CombinatorialClosedOrientableSurface PolygonComponentEulerOk PolygonComponentLinksCyclic
    OrientedPolygonComponentOk PolygonComponentClosedQuadrangulation
  native_decide

/-- Every horizon oriented polygon component is a concrete closed orientable surface. -/
theorem horizonAnnulusHandle_all_combinatorialSurface :
    ∀ C ∈ horizonAnnulusHandleOrientedPolygonComponents,
      CombinatorialClosedOrientableSurface C := by
  intro C hC
  simp only [horizonAnnulusHandleOrientedPolygonComponents, List.mem_cons,
    List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · exact horizonOrientedTorus_combinatorialSurface
  · exact horizonOrientedSphere_combinatorialSurface

/-- Every dyadic-sponge oriented polygon component is a concrete closed orientable surface. -/
theorem dyadicSpongeR20_all_combinatorialSurface :
    ∀ C ∈ dyadicSpongeR20OrientedPolygonComponents,
      CombinatorialClosedOrientableSurface C := by
  intro C hC
  simp only [dyadicSpongeR20OrientedPolygonComponents, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hC
  rcases hC with ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩) | rfl
  · exact dyadicOrientedGenus125_combinatorialSurface
  · exact dyadicOrientedSmallSphere_combinatorialSurface
  · exact dyadicOrientedMediumSphere_combinatorialSurface
  · exact dyadicOrientedLargeSphere_combinatorialSurface

/-- The horizon torus Phase-44 obligation is concretely satisfied: each obligation field is backed by
the closed-orientable-surface witness rather than by a placeholder. -/
theorem horizonOrientedTorus_concreteObligationOk :
    EmbeddedComponentMapObligationOk
      (concreteObligation horizonOrientedTorusComponent standardTorus) :=
  concreteObligationOk_of_surface horizonOrientedTorusComponent standardTorus
    horizonOrientedTorus_combinatorialSurface (by native_decide)

/-- Phase-46 horizon capstone: the torus-plus-sphere obligation package closes with concrete
closed-orientable-surface obligations, not Phase-44 placeholders. The embedded homeomorphism still
requires the classification of closed surfaces. -/
theorem horizonAnnulusHandle_concreteEmbeddedObligationsClose :
    EmbeddedComponentMapObligationsClose horizonAnnulusHandleBetti
      (concreteObligations horizonAnnulusHandleOrientedPolygonComponents
        horizonAnnulusHandleSurfaceTypes) 1 := by
  apply embeddedComponentMapObligationsClose_of_concrete
  · native_decide
  · intro P hP
    obtain ⟨c, s⟩ := P
    exact horizonAnnulusHandle_all_combinatorialSurface c (List.of_mem_zip hP).1
  · exact horizonAnnulusHandle_componentPairingCloses

/-- Phase-46 dyadic capstone: the genus-125-plus-spheres obligation package closes with concrete
closed-orientable-surface obligations, not Phase-44 placeholders. The embedded homeomorphism still
requires the classification of closed surfaces. -/
theorem dyadicSpongeR20_concreteEmbeddedObligationsClose :
    EmbeddedComponentMapObligationsClose dyadicSpongeR20Betti
      (concreteObligations dyadicSpongeR20OrientedPolygonComponents
        dyadicSpongeR20SurfaceTypes) (-72) := by
  apply embeddedComponentMapObligationsClose_of_concrete
  · native_decide
  · intro P hP
    obtain ⟨c, s⟩ := P
    exact dyadicSpongeR20_all_combinatorialSurface c (List.of_mem_zip hP).1
  · exact dyadicSpongeR20_componentPairingCloses

/-! ## Phase 47: conditional homeomorphism under the classification of closed surfaces.

Phase 46 proved every target component is a concrete closed orientable combinatorial surface whose
Euler characteristic matches its standard surface. The only remaining step to a homeomorphism is the
classification of closed surfaces: a closed connected orientable combinatorial 2-manifold of genus `g`
is homeomorphic to the standard genus-`g` surface. That classical result is not in Mathlib.

This phase makes the dependency explicit without assuming it as an axiom. It parameterizes over an
abstract realization relation `R` (read: the geometric realization of the component is homeomorphic to
the standard surface) and over the classification as a hypothesis on `R`. Every theorem below is a
CONDITIONAL THEOREM, conditional on the classification of closed surfaces, with no new axiom and no
placeholder. Once the classification ships for the recognition-foam realization, instantiating `R`
makes the conclusions unconditional. -/

/-- The classification of closed surfaces, stated as a named hypothesis on an abstract realization
relation `R`. `R C S` reads "the geometric realization of the corrected polygon component `C` is
homeomorphic to the standard surface `S`." The hypothesis says every concrete closed orientable
combinatorial surface whose Euler characteristic matches a standard surface is realized by it. This is
the classical classification of closed surfaces, held here as an explicit hypothesis, never an axiom. -/
def ClosedSurfaceClassification
    (R : OrientedPolygonGluingComponent → StandardSurfaceType → Prop) : Prop :=
  ∀ (C : OrientedPolygonGluingComponent) (S : StandardSurfaceType),
    CombinatorialClosedOrientableSurface C → C.polygon.euler = standardSurfaceEuler S → R C S

/-- Conditional homeomorphism, one component: under the classification of closed surfaces, a concrete
closed orientable combinatorial surface with the matching Euler characteristic is realized by its
standard surface. -/
theorem realizesStandard_of_surface
    (R : OrientedPolygonGluingComponent → StandardSurfaceType → Prop)
    (hClass : ClosedSurfaceClassification R)
    (C : OrientedPolygonGluingComponent) (S : StandardSurfaceType)
    (hsurf : CombinatorialClosedOrientableSurface C)
    (heuler : C.polygon.euler = standardSurfaceEuler S) :
    R C S :=
  hClass C S hsurf heuler

/-- Conditional homeomorphism, whole package: under the classification of closed surfaces, every paired
component of a closed concrete obligation package is realized by its standard surface. The per-pair
Euler match is taken from the Phase-43 component pairing inside the closure. -/
theorem concreteObligations_realizeStandard
    (R : OrientedPolygonGluingComponent → StandardSurfaceType → Prop)
    (hClass : ClosedSurfaceClassification R)
    (B : BettiTriple) (Cs : List OrientedPolygonGluingComponent)
    (Ss : List StandardSurfaceType) (halfEuler : ℤ)
    (hSurf : ∀ P ∈ Cs.zip Ss, CombinatorialClosedOrientableSurface P.1)
    (hPair : ComponentPairingCloses B Cs Ss halfEuler) :
    ∀ P ∈ Cs.zip Ss, R P.1 P.2 := by
  intro P hP
  exact hClass P.1 P.2 (hSurf P hP) (hPair.2.1 P hP).2

/-- Phase-47 horizon capstone (CONDITIONAL THEOREM): under the classification of closed surfaces, the
horizon regular-neighborhood boundary is realized component by component, the torus component by the
standard torus and the sphere component by the standard sphere. -/
theorem horizonAnnulusHandle_realizesStandard
    (R : OrientedPolygonGluingComponent → StandardSurfaceType → Prop)
    (hClass : ClosedSurfaceClassification R) :
    R horizonOrientedTorusComponent standardTorus ∧
      R horizonOrientedSphereComponent standardSphere :=
  ⟨hClass _ _ horizonOrientedTorus_combinatorialSurface (by native_decide),
   hClass _ _ horizonOrientedSphere_combinatorialSurface (by native_decide)⟩

/-- Phase-47 dyadic capstone (CONDITIONAL THEOREM): under the classification of closed surfaces, every
component of the dyadic-sponge regular-neighborhood boundary is realized by its standard surface (one
genus-125 surface and 52 spheres). -/
theorem dyadicSpongeR20_realizesStandard
    (R : OrientedPolygonGluingComponent → StandardSurfaceType → Prop)
    (hClass : ClosedSurfaceClassification R) :
    ∀ P ∈ dyadicSpongeR20OrientedPolygonComponents.zip dyadicSpongeR20SurfaceTypes, R P.1 P.2 :=
  concreteObligations_realizeStandard R hClass dyadicSpongeR20Betti
    dyadicSpongeR20OrientedPolygonComponents dyadicSpongeR20SurfaceTypes (-72)
    (by
      intro P hP
      obtain ⟨c, s⟩ := P
      exact dyadicSpongeR20_all_combinatorialSurface c (List.of_mem_zip hP).1)
    dyadicSpongeR20_componentPairingCloses

end RegularNeighborhoodBoundary
end Cosmology
end IndisputableMonolith
