/-
  PrimitiveRecognitionCalculus/FormalSystem.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 12: define expressivity and embeddings in enough
    generality to prove the inevitability surface.

  This module is not claiming that every historical foundation has already
  been parsed into the interface. It closes the exact theorem-shaped interface:
  any formal system that supplies distinguishable endpoint tokens and preserves
  trace extension admits a PRC trace embedding.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.TraceLogic

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Minimal formal-system interface needed by the PRC inevitability theorem.
`Token` and `Expr` are verifier-side carriers for an arbitrary formal system,
while `distinguishes` and `exprExtends` record the structure that makes δ
visible inside it. -/
structure FormalSystem where
  Token : Type
  Expr : Type
  distinguishes : Token → Token → Prop
  exprExtends : Expr → Expr → Prop
  endpointToken : Endpoint → Token
  traceExpr : Trace → Expr
  traceExpr_extends :
    ∀ {T U : Trace}, Trace.Extends T U → exprExtends (traceExpr T) (traceExpr U)

namespace FormalSystem

/-- A formal system is expressive for the first inevitability pass when it can
distinguish the two endpoints of the primitive distinction. -/
def Expressive (F : FormalSystem) : Prop :=
  F.distinguishes (F.endpointToken Endpoint.left) (F.endpointToken Endpoint.right)

end FormalSystem

/-- A PRC embedding into a formal system preserves the primitive endpoint
distinction and finite trace extension. -/
structure PRCEmbeddingInto (F : FormalSystem) where
  endpointMap : Endpoint → F.Token
  traceMap : Trace → F.Expr
  preserves_distinction :
    F.distinguishes (endpointMap Endpoint.left) (endpointMap Endpoint.right)
  preserves_trace_extension :
    ∀ {T U : Trace}, Trace.Extends T U → F.exprExtends (traceMap T) (traceMap U)

/-- The canonical embedding supplied by an expressive formal system's own trace
and endpoint interpretation fields. -/
def PRCEmbeddingInto.ofExpressive
    (F : FormalSystem) (hF : F.Expressive) : PRCEmbeddingInto F where
  endpointMap := F.endpointToken
  traceMap := F.traceExpr
  preserves_distinction := hF
  preserves_trace_extension := F.traceExpr_extends

/-- Exact target for Build Order step 12. -/
def FormalSystemEmbeddingTarget : Prop :=
  ∀ F : FormalSystem, F.Expressive → Nonempty (PRCEmbeddingInto F)

theorem FormalSystemEmbeddingTarget_proved :
    FormalSystemEmbeddingTarget := by
  intro F hF
  exact ⟨PRCEmbeddingInto.ofExpressive F hF⟩

theorem Endpoint.left_ne_right :
    Endpoint.left ≠ Endpoint.right := by
  intro h
  have hside := congrArg Endpoint.side h
  cases hside

/-- PRC itself as the minimal formal system: endpoint tokens are endpoints,
expressions are finite traces, and expression extension is trace extension. -/
def PRCFormalSystem : FormalSystem where
  Token := Endpoint
  Expr := Trace
  distinguishes := fun a b => a ≠ b
  exprExtends := Trace.Extends
  endpointToken := id
  traceExpr := id
  traceExpr_extends := by
    intro T U hTU
    exact hTU

theorem PRCFormalSystem_expressive :
    PRCFormalSystem.Expressive := by
  exact Endpoint.left_ne_right

theorem PRCFormalSystem_embedding :
    Nonempty (PRCEmbeddingInto PRCFormalSystem) :=
  FormalSystemEmbeddingTarget_proved PRCFormalSystem PRCFormalSystem_expressive

/-- Step 12 certificate: the formal-system surface and embedding theorem are
closed. The broader claim that every external foundation satisfies this
interface is the next inevitability layer, not hidden here. -/
structure FormalSystemCertificate : Prop where
  formal_system_surface : Nonempty FormalSystem
  prc_system_expressive : PRCFormalSystem.Expressive
  prc_system_embedding : Nonempty (PRCEmbeddingInto PRCFormalSystem)
  embedding_target : FormalSystemEmbeddingTarget
  embedding_from_expressive :
    ∀ F : FormalSystem, F.Expressive → Nonempty (PRCEmbeddingInto F)
  strength_tag : StrengthTag.deltaOnly = StrengthTag.deltaOnly

theorem formal_system_certificate : FormalSystemCertificate where
  formal_system_surface := ⟨PRCFormalSystem⟩
  prc_system_expressive := PRCFormalSystem_expressive
  prc_system_embedding := PRCFormalSystem_embedding
  embedding_target := FormalSystemEmbeddingTarget_proved
  embedding_from_expressive := FormalSystemEmbeddingTarget_proved
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith
