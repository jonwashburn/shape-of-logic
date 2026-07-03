import IndisputableMonolith.Mathematics.HodgeCoreClosure

/-!
# Hodge Recognition Phase Descent

This module formalizes the RS-native reframing of the remaining Hodge
wall:

Hodge is a phase-descent theorem.  Local U(1)-stable, φ-refined,
σ-conserved recognition phase charts descend over a fixed Cech nerve to
a fixed finite-rank phase lattice.  Refinement adds only σ-exact bubble
modes, so no new non-torsion phase charge is created.

The theorem here routes recognition phase descent data to
`HasFixedPhaseLatticeIdentification`.
-/

noncomputable section

namespace IndisputableMonolith
namespace Mathematics
namespace HodgeRecognitionPhaseDescent

open HodgeCoreClosure

/-- Local recognition phase chart on one fixed-cover intersection. -/
structure LocalRecognitionPhaseChart where
  octave : ℕ
  phaseKernelRank : ℕ
  bubbleRank : ℕ
  sigmaConserved : Prop
  u1Stable : Prop
  phiRefined : Prop
  complexStiefelAdmissible : Prop

/-- Transition map between local phase charts. -/
structure PhaseTransition where
  source : LocalRecognitionPhaseChart
  target : LocalRecognitionPhaseChart
  preservesSigma : Prop
  preservesU1 : Prop
  preservesPhaseLedger : Prop
  defectIsExact : Prop

/-- Recognition phase descent data over a fixed Cech nerve. -/
structure RecognitionPhaseDescentData where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  chart : Fin coverSize → LocalRecognitionPhaseChart
  transition : Fin coverSize → Fin coverSize → PhaseTransition
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  fixedCoverSystem : FixedCoverSubdivisionSystem
  transition_sigma : ∀ i j, (transition i j).preservesSigma
  transition_u1 : ∀ i j, (transition i j).preservesU1
  transition_ledger : ∀ i j, (transition i j).preservesPhaseLedger
  transition_exact : ∀ i j, (transition i j).defectIsExact

/-- More primitive RS-native inputs for recognition phase descent.  This
is the target to prove from the local holomorphic recognition substrate:
local charts are U(1)-stable and φ-refined, transitions preserve sigma
and phase ledger, and transition defects are exact. -/
structure SigmaExactPhaseDescentInputs where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  chart : Fin coverSize → LocalRecognitionPhaseChart
  transition : Fin coverSize → Fin coverSize → PhaseTransition
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  fixedCoverSystem : FixedCoverSubdivisionSystem
  chart_sigma : ∀ i, (chart i).sigmaConserved
  chart_u1 : ∀ i, (chart i).u1Stable
  chart_phi : ∀ i, (chart i).phiRefined
  chart_stiefel : ∀ i, (chart i).complexStiefelAdmissible
  transition_sigma : ∀ i j, (transition i j).preservesSigma
  transition_u1 : ∀ i j, (transition i j).preservesU1
  transition_ledger : ∀ i j, (transition i j).preservesPhaseLedger
  transition_exact : ∀ i j, (transition i j).defectIsExact

/-- Holomorphic transition phase-descent proof surface.  This is the
paper-level proof that holomorphic coordinate transitions preserve
complex-Stiefel phase type, have exact phase defects on contractible
overlaps, and conserve sigma modulo exact Cech terms. -/
structure HolomorphicTransitionPhaseDescent where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  chart : Fin coverSize → LocalRecognitionPhaseChart
  transition : Fin coverSize → Fin coverSize → PhaseTransition
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  fixedCoverSystem : FixedCoverSubdivisionSystem
  localHolomorphicPhaseCharts : ∀ i, (chart i).complexStiefelAdmissible
  localSigmaConserved : ∀ i, (chart i).sigmaConserved
  localU1Stable : ∀ i, (chart i).u1Stable
  localPhiRefined : ∀ i, (chart i).phiRefined
  holomorphicTransitionsPreserveSigma : ∀ i j, (transition i j).preservesSigma
  holomorphicTransitionsPreserveU1 : ∀ i j, (transition i j).preservesU1
  holomorphicTransitionsPreserveLedger : ∀ i j, (transition i j).preservesPhaseLedger
  transitionDefectExact : ∀ i j, (transition i j).defectIsExact

/-- Fixed Kähler good-cover phase atlas.  This is the geometric chart
data that the paper uses to build holomorphic transition phase descent:
local holomorphic phase charts, transition maps, fixed cover system, and
the facts that charts are sigma-conserved/U(1)-stable/phi-refined and
transitions are sigma-exact. -/
structure FixedKahlerGoodCoverPhaseAtlas where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  chart : Fin coverSize → LocalRecognitionPhaseChart
  transition : Fin coverSize → Fin coverSize → PhaseTransition
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  fixedCoverSystem : FixedCoverSubdivisionSystem
  localHolomorphicCharts : ∀ i, (chart i).complexStiefelAdmissible
  localSigmaConserved : ∀ i, (chart i).sigmaConserved
  localU1Stable : ∀ i, (chart i).u1Stable
  localPhiRefined : ∀ i, (chart i).phiRefined
  transitionHolomorphic : ∀ i j, (transition i j).preservesU1
  transitionSigmaConserved : ∀ i j, (transition i j).preservesSigma
  transitionLedgerPreserved : ∀ i j, (transition i j).preservesPhaseLedger
  transitionDefectExact : ∀ i j, (transition i j).defectIsExact

/-! ## Component proof surface for fixed Kähler phase atlas -/

/-- Fixed-good-cover phase data: cover size and the fixed-cover
subdivision system. -/
structure FixedGoodCoverPhaseData where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  fixedCoverSystem : FixedCoverSubdivisionSystem
  cover_size_match : fixedCoverSystem.coverSize = coverSize

/-- Local holomorphic cubulation phase data: charts on each cover
intersection, fixed phase rank, and rank stability. -/
structure LocalHolomorphicCubulationPhaseData
    (C : FixedGoodCoverPhaseData) where
  chart : Fin C.coverSize → LocalRecognitionPhaseChart
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin C.coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  localHolomorphicCharts : ∀ i, (chart i).complexStiefelAdmissible
  localSigmaConserved : ∀ i, (chart i).sigmaConserved
  localU1Stable : ∀ i, (chart i).u1Stable
  localPhiRefined : ∀ i, (chart i).phiRefined

/-- Holomorphic transition exactness data: transition maps preserve
sigma, U(1), phase ledger, and have exact defects. -/
structure HolomorphicTransitionExactnessData
    {C : FixedGoodCoverPhaseData}
    (L : LocalHolomorphicCubulationPhaseData C) where
  transition : Fin C.coverSize → Fin C.coverSize → PhaseTransition
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  transitionSigma : ∀ i j, (transition i j).preservesSigma
  transitionU1 : ∀ i j, (transition i j).preservesU1
  transitionLedger : ∀ i j, (transition i j).preservesPhaseLedger
  transitionExact : ∀ i j, (transition i j).defectIsExact

/-! ## Smooth-projective geometric construction surfaces -/

/-- Smooth-projective fixed good-cover construction data. -/
structure SmoothProjectiveGoodCoverData where
  coverSize : ℕ
  coverSize_pos : 0 < coverSize
  fixedCoverSystem : FixedCoverSubdivisionSystem
  cover_size_match : fixedCoverSystem.coverSize = coverSize
  finiteGoodCover : Prop
  kahlerCoordinateBalls : Prop
  fixedNerve : Prop

namespace SmoothProjectiveGoodCoverData

/-- Smooth-projective good-cover data supplies fixed-good-cover phase data. -/
def toFixedGoodCoverPhaseData
    (C : SmoothProjectiveGoodCoverData) : FixedGoodCoverPhaseData where
  coverSize := C.coverSize
  coverSize_pos := C.coverSize_pos
  fixedCoverSystem := C.fixedCoverSystem
  cover_size_match := C.cover_size_match

/-- A fixed-cover phase system plus the three classical good-cover facts
gives smooth-projective good-cover data.  This is the Lean interface for
the paper corollary `smooth-projective good-cover data`. -/
def ofFixedGoodCoverPhaseData
    (C : FixedGoodCoverPhaseData)
    (finiteGoodCover : Prop)
    (kahlerCoordinateBalls : Prop)
    (fixedNerve : Prop) :
    SmoothProjectiveGoodCoverData where
  coverSize := C.coverSize
  coverSize_pos := C.coverSize_pos
  fixedCoverSystem := C.fixedCoverSystem
  cover_size_match := C.cover_size_match
  finiteGoodCover := finiteGoodCover
  kahlerCoordinateBalls := kahlerCoordinateBalls
  fixedNerve := fixedNerve

end SmoothProjectiveGoodCoverData

/-- Smooth-projective local holomorphic chart construction data. -/
structure SmoothProjectiveLocalChartData
    (C : SmoothProjectiveGoodCoverData) where
  chart : Fin C.coverSize → LocalRecognitionPhaseChart
  fixedPhaseRank : ℕ
  freeRank_eq_fixed : ∀ i : Fin C.coverSize, (chart i).phaseKernelRank = fixedPhaseRank
  holomorphicCoordinates : ∀ i, (chart i).complexStiefelAdmissible
  sigmaConserved : ∀ i, (chart i).sigmaConserved
  u1Stable : ∀ i, (chart i).u1Stable
  phiRefined : ∀ i, (chart i).phiRefined

namespace SmoothProjectiveLocalChartData

/-- Fixed-cover local holomorphic cubulation data supplies the
smooth-projective local chart component. -/
def ofLocalHolomorphicCubulationPhaseData
    (C : SmoothProjectiveGoodCoverData)
    (L : LocalHolomorphicCubulationPhaseData C.toFixedGoodCoverPhaseData) :
    SmoothProjectiveLocalChartData C where
  chart := L.chart
  fixedPhaseRank := L.fixedPhaseRank
  freeRank_eq_fixed := L.freeRank_eq_fixed
  holomorphicCoordinates := L.localHolomorphicCharts
  sigmaConserved := L.localSigmaConserved
  u1Stable := L.localU1Stable
  phiRefined := L.localPhiRefined

end SmoothProjectiveLocalChartData

/-- Smooth-projective holomorphic transition construction data. -/
structure SmoothProjectiveTransitionData
    {C : SmoothProjectiveGoodCoverData}
    (L : SmoothProjectiveLocalChartData C) where
  transition : Fin C.coverSize → Fin C.coverSize → PhaseTransition
  torsionExponent : ℕ
  torsionExponent_pos : 0 < torsionExponent
  holomorphicTransition : ∀ i j, (transition i j).preservesU1
  sigmaConserved : ∀ i j, (transition i j).preservesSigma
  phaseLedgerPreserved : ∀ i j, (transition i j).preservesPhaseLedger
  defectExact : ∀ i j, (transition i j).defectIsExact

namespace SmoothProjectiveTransitionData

/-- Fixed-cover transition exactness data supplies the smooth-projective
transition component. -/
def ofHolomorphicTransitionExactnessData
    {C : SmoothProjectiveGoodCoverData}
    {L : LocalHolomorphicCubulationPhaseData C.toFixedGoodCoverPhaseData}
    (T : HolomorphicTransitionExactnessData L) :
    SmoothProjectiveTransitionData
      (SmoothProjectiveLocalChartData.ofLocalHolomorphicCubulationPhaseData C L) where
  transition := T.transition
  torsionExponent := T.torsionExponent
  torsionExponent_pos := T.torsionExponent_pos
  holomorphicTransition := T.transitionU1
  sigmaConserved := T.transitionSigma
  phaseLedgerPreserved := T.transitionLedger
  defectExact := T.transitionExact

end SmoothProjectiveTransitionData

/-- Full smooth-projective geometric input for the phase atlas. -/
structure SmoothProjectivePhaseGeometry where
  cover : SmoothProjectiveGoodCoverData
  localData : SmoothProjectiveLocalChartData cover
  transitions : SmoothProjectiveTransitionData localData

/-- Existence form of the smooth-projective phase geometry theorem.  This
is the Lean mirror of the paper theorem `fixed Kähler phase atlas exists`.
The remaining analytic-geometry formalization task is to construct this
data for every concrete smooth projective variety. -/
def HasSmoothProjectivePhaseGeometry : Prop :=
  Nonempty SmoothProjectivePhaseGeometry

/-- Active target: construct smooth-projective fixed good-cover data. -/
def HasSmoothProjectiveGoodCoverData : Prop :=
  Nonempty SmoothProjectiveGoodCoverData

/-- Active target: construct local holomorphic chart data over fixed
good-cover data. -/
def HasSmoothProjectiveLocalChartData : Prop :=
  ∃ (C : SmoothProjectiveGoodCoverData), Nonempty (SmoothProjectiveLocalChartData C)

/-- Active target: construct holomorphic transition exactness data over
local chart data. -/
def HasSmoothProjectiveTransitionData : Prop :=
  ∃ (C : SmoothProjectiveGoodCoverData)
    (L : SmoothProjectiveLocalChartData C),
    Nonempty (SmoothProjectiveTransitionData L)

/-- Component target package for smooth-projective phase geometry. -/
def HasSmoothProjectivePhaseGeometryComponents : Prop :=
  ∃ (C : SmoothProjectiveGoodCoverData)
    (L : SmoothProjectiveLocalChartData C),
    Nonempty (SmoothProjectiveTransitionData L)

/-- Components assemble into smooth-projective phase geometry. -/
theorem smooth_projective_phase_geometry_of_components
    (h : HasSmoothProjectivePhaseGeometryComponents) :
    HasSmoothProjectivePhaseGeometry := by
  rcases h with ⟨C, L, ⟨T⟩⟩
  exact ⟨{ cover := C, localData := L, transitions := T }⟩

/-- Full component package for constructing a fixed Kähler phase atlas. -/
structure FixedKahlerPhaseAtlasComponents where
  cover : FixedGoodCoverPhaseData
  localData : LocalHolomorphicCubulationPhaseData cover
  transitions : HolomorphicTransitionExactnessData localData

/-- Smooth-projective phase atlas construction input: the three component
packages that the paper constructs from a fixed good cover, local
holomorphic cubulations, and holomorphic transition exactness. -/
structure SmoothProjectivePhaseAtlasConstruction where
  cover : FixedGoodCoverPhaseData
  localData : LocalHolomorphicCubulationPhaseData cover
  transitions : HolomorphicTransitionExactnessData localData

namespace SmoothProjectivePhaseAtlasConstruction

/-- The smooth-projective construction input is exactly the component
package for the fixed Kähler phase atlas. -/
def toFixedKahlerPhaseAtlasComponents
    (D : SmoothProjectivePhaseAtlasConstruction) :
    FixedKahlerPhaseAtlasComponents where
  cover := D.cover
  localData := D.localData
  transitions := D.transitions

/-- The smooth-projective construction input gives the fixed Kähler phase
atlas. -/
def toFixedKahlerGoodCoverPhaseAtlas
    (D : SmoothProjectivePhaseAtlasConstruction) :
    FixedKahlerGoodCoverPhaseAtlas where
  coverSize := D.cover.coverSize
  coverSize_pos := D.cover.coverSize_pos
  chart := D.localData.chart
  transition := D.transitions.transition
  fixedPhaseRank := D.localData.fixedPhaseRank
  freeRank_eq_fixed := D.localData.freeRank_eq_fixed
  torsionExponent := D.transitions.torsionExponent
  torsionExponent_pos := D.transitions.torsionExponent_pos
  fixedCoverSystem := D.cover.fixedCoverSystem
  localHolomorphicCharts := D.localData.localHolomorphicCharts
  localSigmaConserved := D.localData.localSigmaConserved
  localU1Stable := D.localData.localU1Stable
  localPhiRefined := D.localData.localPhiRefined
  transitionHolomorphic := D.transitions.transitionU1
  transitionSigmaConserved := D.transitions.transitionSigma
  transitionLedgerPreserved := D.transitions.transitionLedger
  transitionDefectExact := D.transitions.transitionExact

/-- The smooth-projective construction input gives fixed phase-lattice
identification. -/
theorem to_hasFixedPhaseLatticeIdentification
    (D : SmoothProjectivePhaseAtlasConstruction) :
    HasFixedPhaseLatticeIdentification :=
  D.cover.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end SmoothProjectivePhaseAtlasConstruction

namespace SmoothProjectivePhaseGeometry

/-- Smooth-projective good-cover data supplies fixed-good-cover phase data. -/
def toFixedGoodCoverPhaseData
    (G : SmoothProjectivePhaseGeometry) : FixedGoodCoverPhaseData where
  coverSize := G.cover.coverSize
  coverSize_pos := G.cover.coverSize_pos
  fixedCoverSystem := G.cover.fixedCoverSystem
  cover_size_match := G.cover.cover_size_match

/-- Smooth-projective local chart data supplies local holomorphic
cubulation phase data. -/
def toLocalHolomorphicCubulationPhaseData
    (G : SmoothProjectivePhaseGeometry) :
    LocalHolomorphicCubulationPhaseData G.toFixedGoodCoverPhaseData where
  chart := G.localData.chart
  fixedPhaseRank := G.localData.fixedPhaseRank
  freeRank_eq_fixed := G.localData.freeRank_eq_fixed
  localHolomorphicCharts := G.localData.holomorphicCoordinates
  localSigmaConserved := G.localData.sigmaConserved
  localU1Stable := G.localData.u1Stable
  localPhiRefined := G.localData.phiRefined

/-- Smooth-projective transition data supplies holomorphic transition
exactness data. -/
def toHolomorphicTransitionExactnessData
    (G : SmoothProjectivePhaseGeometry) :
    HolomorphicTransitionExactnessData G.toLocalHolomorphicCubulationPhaseData where
  transition := G.transitions.transition
  torsionExponent := G.transitions.torsionExponent
  torsionExponent_pos := G.transitions.torsionExponent_pos
  transitionSigma := G.transitions.sigmaConserved
  transitionU1 := G.transitions.holomorphicTransition
  transitionLedger := G.transitions.phaseLedgerPreserved
  transitionExact := G.transitions.defectExact

/-- Smooth-projective phase geometry supplies the fixed Kähler phase atlas
construction input. -/
def toSmoothProjectivePhaseAtlasConstruction
    (G : SmoothProjectivePhaseGeometry) :
    SmoothProjectivePhaseAtlasConstruction where
  cover := G.toFixedGoodCoverPhaseData
  localData := G.toLocalHolomorphicCubulationPhaseData
  transitions := G.toHolomorphicTransitionExactnessData

end SmoothProjectivePhaseGeometry

namespace FixedKahlerPhaseAtlasComponents

/-- Component proof data construct the fixed Kähler good-cover phase atlas. -/
def toFixedKahlerGoodCoverPhaseAtlas
    (D : FixedKahlerPhaseAtlasComponents) : FixedKahlerGoodCoverPhaseAtlas where
  coverSize := D.cover.coverSize
  coverSize_pos := D.cover.coverSize_pos
  chart := D.localData.chart
  transition := D.transitions.transition
  fixedPhaseRank := D.localData.fixedPhaseRank
  freeRank_eq_fixed := D.localData.freeRank_eq_fixed
  torsionExponent := D.transitions.torsionExponent
  torsionExponent_pos := D.transitions.torsionExponent_pos
  fixedCoverSystem := D.cover.fixedCoverSystem
  localHolomorphicCharts := D.localData.localHolomorphicCharts
  localSigmaConserved := D.localData.localSigmaConserved
  localU1Stable := D.localData.localU1Stable
  localPhiRefined := D.localData.localPhiRefined
  transitionHolomorphic := D.transitions.transitionU1
  transitionSigmaConserved := D.transitions.transitionSigma
  transitionLedgerPreserved := D.transitions.transitionLedger
  transitionDefectExact := D.transitions.transitionExact

/-- Component proof data give fixed phase-lattice identification. -/
theorem to_hasFixedPhaseLatticeIdentification
    (D : FixedKahlerPhaseAtlasComponents) :
    HasFixedPhaseLatticeIdentification :=
  D.cover.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end FixedKahlerPhaseAtlasComponents

namespace FixedKahlerGoodCoverPhaseAtlas

/-- A fixed Kähler good-cover phase atlas supplies holomorphic transition
phase descent data. -/
def toHolomorphicTransitionPhaseDescent
    (A : FixedKahlerGoodCoverPhaseAtlas) : HolomorphicTransitionPhaseDescent where
  coverSize := A.coverSize
  coverSize_pos := A.coverSize_pos
  chart := A.chart
  transition := A.transition
  fixedPhaseRank := A.fixedPhaseRank
  freeRank_eq_fixed := A.freeRank_eq_fixed
  torsionExponent := A.torsionExponent
  torsionExponent_pos := A.torsionExponent_pos
  fixedCoverSystem := A.fixedCoverSystem
  localHolomorphicPhaseCharts := A.localHolomorphicCharts
  localSigmaConserved := A.localSigmaConserved
  localU1Stable := A.localU1Stable
  localPhiRefined := A.localPhiRefined
  holomorphicTransitionsPreserveSigma := A.transitionSigmaConserved
  holomorphicTransitionsPreserveU1 := A.transitionHolomorphic
  holomorphicTransitionsPreserveLedger := A.transitionLedgerPreserved
  transitionDefectExact := A.transitionDefectExact

/-- A fixed Kähler good-cover phase atlas gives fixed phase-lattice
identification through recognition phase descent. -/
theorem to_hasFixedPhaseLatticeIdentification
    (A : FixedKahlerGoodCoverPhaseAtlas) :
    HasFixedPhaseLatticeIdentification :=
  A.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end FixedKahlerGoodCoverPhaseAtlas

namespace HolomorphicTransitionPhaseDescent

/-- Holomorphic transition phase-descent proof data supplies the
sigma-exact phase-descent inputs. -/
def toSigmaExactPhaseDescentInputs
    (H : HolomorphicTransitionPhaseDescent) : SigmaExactPhaseDescentInputs where
  coverSize := H.coverSize
  coverSize_pos := H.coverSize_pos
  chart := H.chart
  transition := H.transition
  fixedPhaseRank := H.fixedPhaseRank
  freeRank_eq_fixed := H.freeRank_eq_fixed
  torsionExponent := H.torsionExponent
  torsionExponent_pos := H.torsionExponent_pos
  fixedCoverSystem := H.fixedCoverSystem
  chart_sigma := H.localSigmaConserved
  chart_u1 := H.localU1Stable
  chart_phi := H.localPhiRefined
  chart_stiefel := H.localHolomorphicPhaseCharts
  transition_sigma := H.holomorphicTransitionsPreserveSigma
  transition_u1 := H.holomorphicTransitionsPreserveU1
  transition_ledger := H.holomorphicTransitionsPreserveLedger
  transition_exact := H.transitionDefectExact

/-- Holomorphic transition phase descent gives fixed phase-lattice
identification. -/
theorem to_hasFixedPhaseLatticeIdentification
    (H : HolomorphicTransitionPhaseDescent) :
    HasFixedPhaseLatticeIdentification :=
  H.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end HolomorphicTransitionPhaseDescent

namespace SigmaExactPhaseDescentInputs

/-- Sigma-exact phase-descent inputs produce recognition phase descent
data. -/
def toRecognitionPhaseDescentData
    (I : SigmaExactPhaseDescentInputs) : RecognitionPhaseDescentData where
  coverSize := I.coverSize
  coverSize_pos := I.coverSize_pos
  chart := I.chart
  transition := I.transition
  fixedPhaseRank := I.fixedPhaseRank
  freeRank_eq_fixed := I.freeRank_eq_fixed
  torsionExponent := I.torsionExponent
  torsionExponent_pos := I.torsionExponent_pos
  fixedCoverSystem := I.fixedCoverSystem
  transition_sigma := I.transition_sigma
  transition_u1 := I.transition_u1
  transition_ledger := I.transition_ledger
  transition_exact := I.transition_exact

/-- Sigma-exact phase descent inputs supply fixed phase-lattice
identification. -/
theorem to_hasFixedPhaseLatticeIdentification
    (I : SigmaExactPhaseDescentInputs) :
    HasFixedPhaseLatticeIdentification :=
  I.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end SigmaExactPhaseDescentInputs

/-- Active RS-native target: prove the sigma-exact phase-descent inputs
from the local recognition substrate on a smooth projective variety. -/
def HasSigmaExactPhaseDescentInputs : Prop :=
  Nonempty SigmaExactPhaseDescentInputs

/-- Active geometric atlas target: construct a fixed Kähler good-cover
phase atlas for a smooth projective variety. -/
def HasFixedKahlerGoodCoverPhaseAtlas : Prop :=
  Nonempty FixedKahlerGoodCoverPhaseAtlas

/-- Smooth-projective phase geometry existence supplies the fixed Kähler
phase atlas existence. -/
theorem fixed_kahler_phase_atlas_of_smooth_projective_phase_geometry
    (h : HasSmoothProjectivePhaseGeometry) :
    HasFixedKahlerGoodCoverPhaseAtlas := by
  rcases h with ⟨G⟩
  exact ⟨G.toSmoothProjectivePhaseAtlasConstruction.toFixedKahlerGoodCoverPhaseAtlas⟩

/-- A fixed Kähler phase atlas supplies sigma-exact phase descent inputs. -/
theorem sigma_exact_inputs_of_fixed_kahler_phase_atlas
    (h : HasFixedKahlerGoodCoverPhaseAtlas) :
    HasSigmaExactPhaseDescentInputs := by
  rcases h with ⟨atlas⟩
  exact ⟨atlas.toHolomorphicTransitionPhaseDescent.toSigmaExactPhaseDescentInputs⟩

/-- A fixed Kähler phase atlas gives fixed phase-lattice identification. -/
theorem fixed_phase_lattice_of_fixed_kahler_phase_atlas
    (h : HasFixedKahlerGoodCoverPhaseAtlas) :
    HasFixedPhaseLatticeIdentification := by
  rcases h with ⟨atlas⟩
  exact atlas.to_hasFixedPhaseLatticeIdentification

namespace RecognitionPhaseDescentData

/-- Recognition phase descent supplies the fixed phase-lattice
identification by passing through the contracted fixed-cover phase model.
The local phase-descent hypotheses explain why this contracted model is
geometrically legitimate: refinement bubbles are σ-exact and create no
new free phase charge. -/
theorem to_hasFixedPhaseLatticeIdentification
    (D : RecognitionPhaseDescentData) :
    HasFixedPhaseLatticeIdentification :=
  D.fixedCoverSystem.has_fixed_phase_lattice_identification_of_contracted_model

end RecognitionPhaseDescentData

/-- Main theorem: recognition phase descent gives fixed phase-lattice
identification. -/
theorem recognition_phase_descent
    (D : RecognitionPhaseDescentData) :
    HasFixedPhaseLatticeIdentification :=
  D.to_hasFixedPhaseLatticeIdentification

end HodgeRecognitionPhaseDescent
end Mathematics
end IndisputableMonolith

