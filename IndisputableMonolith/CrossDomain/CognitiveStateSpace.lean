import Mathlib

/-!
# C1: Cognitive State Space — 5³ = 125 — Wave 62 Cross-Domain

Structural claim: the conscious moment is spanned by three orthogonal
recognition axes, each of configDim D = 5:

  Sense × Emotion × MemorySystem  =  5 × 5 × 5  =  125.

This module does four things:
1. Defines the three factor types, each of cardinality 5.
2. Defines the product type `CognitiveState` and proves `|CognitiveState| = 125`.
3. Proves each projection is surjective (the product is non-degenerate).
4. Proves non-reducibility: the product is strictly larger than any factor.

What this does NOT prove: that these three axes are empirically independent
in neural data. That is a testable hypothesis about EEG decoders, not a Lean
theorem. The Lean content here is: IF the three-fold decomposition holds,
THEN the state space has the enumerated structure.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.CrossDomain.CognitiveStateSpace

inductive Sense where
  | sight | hearing | touch | smell | taste
  deriving DecidableEq, Repr, BEq, Fintype

inductive Emotion where
  | joy | sadness | fear | anger | disgust
  deriving DecidableEq, Repr, BEq, Fintype

inductive MemorySystem where
  | working | episodic | semantic | procedural | priming
  deriving DecidableEq, Repr, BEq, Fintype

theorem senseCount : Fintype.card Sense = 5 := by decide
theorem emotionCount : Fintype.card Emotion = 5 := by decide
theorem memorySystemCount : Fintype.card MemorySystem = 5 := by decide

abbrev CognitiveState : Type := Sense × Emotion × MemorySystem

theorem cognitiveStateCount : Fintype.card CognitiveState = 125 := by
  simp only [CognitiveState, Fintype.card_prod, senseCount, emotionCount, memorySystemCount]

/-- Sense projection is surjective. -/
theorem senseProj_surj : Function.Surjective (fun s : CognitiveState => s.1) := by
  intro x; exact ⟨(x, Emotion.joy, MemorySystem.working), rfl⟩

/-- Emotion projection is surjective. -/
theorem emotionProj_surj :
    Function.Surjective (fun s : CognitiveState => s.2.1) := by
  intro x; exact ⟨(Sense.sight, x, MemorySystem.working), rfl⟩

/-- Memory projection is surjective. -/
theorem memoryProj_surj :
    Function.Surjective (fun s : CognitiveState => s.2.2) := by
  intro x; exact ⟨(Sense.sight, Emotion.joy, x), rfl⟩

/-- Non-reducibility: the product is strictly larger than any single factor. -/
theorem notCollapsedToSense : Fintype.card CognitiveState > Fintype.card Sense := by
  rw [cognitiveStateCount, senseCount]; decide

theorem notCollapsedToEmotion :
    Fintype.card CognitiveState > Fintype.card Emotion := by
  rw [cognitiveStateCount, emotionCount]; decide

theorem notCollapsedToMemory :
    Fintype.card CognitiveState > Fintype.card MemorySystem := by
  rw [cognitiveStateCount, memorySystemCount]; decide

/-- The product is strictly larger than any pairwise factor too. -/
theorem notCollapsedToPair1 :
    Fintype.card CognitiveState > Fintype.card (Sense × Emotion) := by
  have h : Fintype.card (Sense × Emotion) = 25 := by
    simp only [Fintype.card_prod, senseCount, emotionCount]
  rw [cognitiveStateCount, h]; decide

theorem notCollapsedToPair2 :
    Fintype.card CognitiveState > Fintype.card (Sense × MemorySystem) := by
  have h : Fintype.card (Sense × MemorySystem) = 25 := by
    simp only [Fintype.card_prod, senseCount, memorySystemCount]
  rw [cognitiveStateCount, h]; decide

theorem notCollapsedToPair3 :
    Fintype.card CognitiveState > Fintype.card (Emotion × MemorySystem) := by
  have h : Fintype.card (Emotion × MemorySystem) = 25 := by
    simp only [Fintype.card_prod, emotionCount, memorySystemCount]
  rw [cognitiveStateCount, h]; decide

structure CognitiveStateSpaceCert where
  product_count : Fintype.card CognitiveState = 125
  sense_surj : Function.Surjective (fun s : CognitiveState => s.1)
  emotion_surj : Function.Surjective (fun s : CognitiveState => s.2.1)
  memory_surj : Function.Surjective (fun s : CognitiveState => s.2.2)
  irreducible_1 : Fintype.card CognitiveState > Fintype.card Sense
  irreducible_2 : Fintype.card CognitiveState > Fintype.card Emotion
  irreducible_3 : Fintype.card CognitiveState > Fintype.card MemorySystem
  irreducible_pair : Fintype.card CognitiveState >
    Fintype.card (Sense × Emotion)

def cognitiveStateSpaceCert : CognitiveStateSpaceCert where
  product_count := cognitiveStateCount
  sense_surj := senseProj_surj
  emotion_surj := emotionProj_surj
  memory_surj := memoryProj_surj
  irreducible_1 := notCollapsedToSense
  irreducible_2 := notCollapsedToEmotion
  irreducible_3 := notCollapsedToMemory
  irreducible_pair := notCollapsedToPair1

end IndisputableMonolith.CrossDomain.CognitiveStateSpace
