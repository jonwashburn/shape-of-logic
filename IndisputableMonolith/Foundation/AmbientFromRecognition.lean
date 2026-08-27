import Mathlib
import IndisputableMonolith.Foundation.GaugeFromCube
import IndisputableMonolith.Foundation.SubstrateAxioms
import IndisputableMonolith.Foundation.RecognitionProducedEmbedding
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure

/-!
# Ambient from recognition data

Anil Q1 / Milan 2: what constructs the ambient M from Recognition?

The honest tokens in `SubstrateAxioms` do not construct it. `CellularCompletion`
and `OneAcyclicSubstrate` are empty packaging types, inhabited in every D by
`trivial`. That is a WALL against reading those tokens as a manifold
construction.

What Recognition does supply, already proved:

* Q₃ has 8 vertices, 12 edges, 6 faces; the cube 2-skeleton has Euler
  characteristic 2
* a detecting embedding S¹ ↪ S³ produced from the hierarchy
  (`RecognitionProducedEmbedding`)
* the working ambient of the closed D=3 theorems is S^D by type

The remaining filling of the cube 2-skeleton to a 3-ball / S³ is MODEL.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace AmbientFromRecognition

open GaugeFromCube
open SubstrateAxioms
open RecognitionProducedEmbedding
open LinkingFromHierarchy

/-- Recognition's 3-cube vertex set. -/
abbrev Q3 := CubeVertex 3

theorem q3_vertex_count : Fintype.card Q3 = 8 :=
  cube3_vertex_count

theorem q3_edge_count : cube_edge_count 3 = 12 :=
  cube3_edge_count

theorem q3_face_count : cube_face_count 3 = 6 :=
  cube3_face_count

/-- Euler characteristic of the cube 2-skeleton: 8 − 12 + 6 = 2. -/
theorem cube_2skeleton_euler : (8 : ℤ) - 12 + 6 = 2 := by decide

theorem cube_2skeleton_euler_from_counts :
    (Fintype.card Q3 : ℤ) - cube_edge_count 3 + cube_face_count 3 = 2 := by
  rw [q3_vertex_count, q3_edge_count, q3_face_count]
  decide

/-- WALL: the SubstrateAxioms completion token is inhabited in every
dimension, so it does not construct M and does not select D. -/
theorem cellular_completion_token_inhabits_every_D (D : ℕ) :
    CellularCompletion D :=
  cellular_completion_trivial D

theorem one_acyclic_token_inhabits_every_D (D : ℕ) :
    OneAcyclicSubstrate D :=
  one_acyclic_trivial D

theorem substrate_tokens_do_not_select_dimension :
    (∀ D, CellularCompletion D) ∧ (∀ D, OneAcyclicSubstrate D) :=
  ⟨cellular_completion_token_inhabits_every_D,
    one_acyclic_token_inhabits_every_D⟩

/-- Recognition produces a detecting embedding into S³. That is the working
ambient of the closed chain, by type, not by SubstrateAxioms. -/
theorem recognition_supplies_detecting_S3 :
    Topology.IsEmbedding
        (recognitionProducedEmbedding
          jRealizedHierarchy.1 jRealizedHierarchy.2) ∧
      PublicSpine.DetectsNontrivialLinking 3 :=
  ⟨recognitionProducedEmbedding_isEmbedding
      jRealizedHierarchy.1 jRealizedHierarchy.2,
    recognition_produced_detects
      jRealizedHierarchy.1 jRealizedHierarchy.2⟩

/-- The closed uniqueness half: a detecting ambient sphere is S³. -/
theorem detecting_sphere_is_three
    {D : ℕ} (h : PublicSpine.DetectsNontrivialLinking D) : D = 3 :=
  PublicSpineLinkingClosure.forces_D3 D h

/-- MODEL remaining: filling the cube 2-skeleton (χ = 2) to a 3-ball whose
boundary is identified with that skeleton. No smooth-manifold constructor
is in scope. -/
structure CubeFillingModel : Prop where
  euler : (Fintype.card Q3 : ℤ) - cube_edge_count 3 + cube_face_count 3 = 2

theorem cubeFillingModel_holds : CubeFillingModel where
  euler := cube_2skeleton_euler_from_counts

end AmbientFromRecognition
end Foundation
end IndisputableMonolith
