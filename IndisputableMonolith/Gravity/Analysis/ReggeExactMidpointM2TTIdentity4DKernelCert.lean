import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeExactFlatHessianBlochData4D

/-!
# Kernel certificates for midpoint m² TT identity (generated)

Script: `scripts/qg/regge_4d_m2_kernel_certs_20260721.py`.
Int List.foldl + scale-32 tables; kernel `decide` only (no `native_decide`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeExactMidpointM2TTIdentity4D
namespace KernelCert

open ReggeExactFlatHessianBlochData4D

set_option maxRecDepth 100000
set_option maxHeartbeats 200000000

structure CZ where
  num : Int
  den : Nat
  de0 : Int
  de1 : Int
  de2 : Int
  de3 : Int
  dep0 : Int
  dep1 : Int
  dep2 : Int
  dep3 : Int
  d0 : Int
  d1 : Int
  d2 : Int
  d3 : Int
deriving DecidableEq

def toCZ (c : Coupling) : CZ :=
  ⟨c.num, c.den, c.De 0, c.De 1, c.De 2, c.De 3,
    c.Dep 0, c.Dep 1, c.Dep 2, c.Dep 3,
    c.delta2 0, c.delta2 1, c.delta2 2, c.delta2 3⟩

@[inline] def De (c : CZ) (a : Fin 4) : Int :=
  match a with | 0 => c.de0 | 1 => c.de1 | 2 => c.de2 | 3 => c.de3
@[inline] def Dep (c : CZ) (a : Fin 4) : Int :=
  match a with | 0 => c.dep0 | 1 => c.dep1 | 2 => c.dep2 | 3 => c.dep3
@[inline] def D2 (c : CZ) (a : Fin 4) : Int :=
  match a with | 0 => c.d0 | 1 => c.d1 | 2 => c.d2 | 3 => c.d3

@[inline] def contrib (c : CZ) (a b cd d i j : Fin 4) : Int :=
  (-c.num) * De c a * De c b * Dep c cd * Dep c d * D2 c i * D2 c j *
    (↑(16 / c.den) : Int)

def czChunk0 : List CZ :=
  [⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩]

def czChunk1 : List CZ :=
  [⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩]

def czChunk2 : List CZ :=
  [⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩]

def czChunk3 : List CZ :=
  [⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩]

def czChunk4 : List CZ :=
  [⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩]

def czChunk5 : List CZ :=
  [⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩]

def czChunk6 : List CZ :=
  [⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (2 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩]

def czChunk7 : List CZ :=
  [⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩]

def czChunk8 : List CZ :=
  [⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩]

def czChunk9 : List CZ :=
  [⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩]

def czChunk10 : List CZ :=
  [⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩]

def czChunk11 : List CZ :=
  [⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩]

def czChunk12 : List CZ :=
  [⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-2 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-2 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (-1 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩]

def czChunk13 : List CZ :=
  [⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩]

def czChunk14 : List CZ :=
  [⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (-1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (-1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(3 : Int), (16 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-3 : Int), (8 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (0 : Int), (1 : Int)⟩]

def czChunk15 : List CZ :=
  [⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (2 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (2 : Int), (1 : Int)⟩,
  ⟨(-1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (0 : Int), (2 : Int), (1 : Int), (1 : Int)⟩,
  ⟨(1 : Int), (4 : Nat), (0 : Int), (0 : Int), (0 : Int), (1 : Int), (0 : Int), (1 : Int), (1 : Int), (0 : Int), (0 : Int), (1 : Int), (1 : Int), (1 : Int)⟩]

theorem czChunk0_bridge :
    couplingChunk0.toList.map toCZ = czChunk0 := by
  decide

theorem czChunk1_bridge :
    couplingChunk1.toList.map toCZ = czChunk1 := by
  decide

theorem czChunk2_bridge :
    couplingChunk2.toList.map toCZ = czChunk2 := by
  decide

theorem czChunk3_bridge :
    couplingChunk3.toList.map toCZ = czChunk3 := by
  decide

theorem czChunk4_bridge :
    couplingChunk4.toList.map toCZ = czChunk4 := by
  decide

theorem czChunk5_bridge :
    couplingChunk5.toList.map toCZ = czChunk5 := by
  decide

theorem czChunk6_bridge :
    couplingChunk6.toList.map toCZ = czChunk6 := by
  decide

theorem czChunk7_bridge :
    couplingChunk7.toList.map toCZ = czChunk7 := by
  decide

theorem czChunk8_bridge :
    couplingChunk8.toList.map toCZ = czChunk8 := by
  decide

theorem czChunk9_bridge :
    couplingChunk9.toList.map toCZ = czChunk9 := by
  decide

theorem czChunk10_bridge :
    couplingChunk10.toList.map toCZ = czChunk10 := by
  decide

theorem czChunk11_bridge :
    couplingChunk11.toList.map toCZ = czChunk11 := by
  decide

theorem czChunk12_bridge :
    couplingChunk12.toList.map toCZ = czChunk12 := by
  decide

theorem czChunk13_bridge :
    couplingChunk13.toList.map toCZ = czChunk13 := by
  decide

theorem czChunk14_bridge :
    couplingChunk14.toList.map toCZ = czChunk14 := by
  decide

theorem czChunk15_bridge :
    couplingChunk15.toList.map toCZ = czChunk15 := by
  decide

def couplingZList : List CZ :=
  czChunk0 ++ czChunk1 ++ czChunk2 ++ czChunk3 ++ czChunk4 ++ czChunk5 ++
    czChunk6 ++ czChunk7 ++ czChunk8 ++ czChunk9 ++ czChunk10 ++ czChunk11 ++
    czChunk12 ++ czChunk13 ++ czChunk14 ++ czChunk15

theorem couplingZList_bridge :
    couplingTable.toList.map toCZ = couplingZList := by
  -- couplingTable is the concatenation of the 16 chunks.
  simp only [couplingTable, List.map_append, Array.toList_append]
  rw [czChunk0_bridge, czChunk1_bridge, czChunk2_bridge, czChunk3_bridge,
      czChunk4_bridge, czChunk5_bridge, czChunk6_bridge, czChunk7_bridge,
      czChunk8_bridge, czChunk9_bridge, czChunk10_bridge, czChunk11_bridge,
      czChunk12_bridge, czChunk13_bridge, czChunk14_bridge, czChunk15_bridge]
  rfl

def m2Num (a b c d i j : Fin 4) : Int :=
  couplingZList.foldl (fun acc t => acc + contrib t a b c d i j) 0

def explicitZ : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int
  | 0, 0, 1, 1, 2, 2 => (4 : Int)
  | 0, 0, 1, 1, 3, 3 => (4 : Int)
  | 0, 0, 1, 2, 1, 2 => (-2 : Int)
  | 0, 0, 1, 2, 2, 1 => (-2 : Int)
  | 0, 0, 1, 3, 1, 3 => (-2 : Int)
  | 0, 0, 1, 3, 3, 1 => (-2 : Int)
  | 0, 0, 2, 1, 1, 2 => (-2 : Int)
  | 0, 0, 2, 1, 2, 1 => (-2 : Int)
  | 0, 0, 2, 2, 1, 1 => (4 : Int)
  | 0, 0, 2, 2, 3, 3 => (4 : Int)
  | 0, 0, 2, 3, 2, 3 => (-2 : Int)
  | 0, 0, 2, 3, 3, 2 => (-2 : Int)
  | 0, 0, 3, 1, 1, 3 => (-2 : Int)
  | 0, 0, 3, 1, 3, 1 => (-2 : Int)
  | 0, 0, 3, 2, 2, 3 => (-2 : Int)
  | 0, 0, 3, 2, 3, 2 => (-2 : Int)
  | 0, 0, 3, 3, 1, 1 => (4 : Int)
  | 0, 0, 3, 3, 2, 2 => (4 : Int)
  | 0, 1, 0, 1, 2, 2 => (-2 : Int)
  | 0, 1, 0, 1, 3, 3 => (-2 : Int)
  | 0, 1, 0, 2, 1, 2 => (1 : Int)
  | 0, 1, 0, 2, 2, 1 => (1 : Int)
  | 0, 1, 0, 3, 1, 3 => (1 : Int)
  | 0, 1, 0, 3, 3, 1 => (1 : Int)
  | 0, 1, 1, 0, 2, 2 => (-2 : Int)
  | 0, 1, 1, 0, 3, 3 => (-2 : Int)
  | 0, 1, 1, 2, 0, 2 => (1 : Int)
  | 0, 1, 1, 2, 2, 0 => (1 : Int)
  | 0, 1, 1, 3, 0, 3 => (1 : Int)
  | 0, 1, 1, 3, 3, 0 => (1 : Int)
  | 0, 1, 2, 0, 1, 2 => (1 : Int)
  | 0, 1, 2, 0, 2, 1 => (1 : Int)
  | 0, 1, 2, 1, 0, 2 => (1 : Int)
  | 0, 1, 2, 1, 2, 0 => (1 : Int)
  | 0, 1, 2, 2, 0, 1 => (-2 : Int)
  | 0, 1, 2, 2, 1, 0 => (-2 : Int)
  | 0, 1, 3, 0, 1, 3 => (1 : Int)
  | 0, 1, 3, 0, 3, 1 => (1 : Int)
  | 0, 1, 3, 1, 0, 3 => (1 : Int)
  | 0, 1, 3, 1, 3, 0 => (1 : Int)
  | 0, 1, 3, 3, 0, 1 => (-2 : Int)
  | 0, 1, 3, 3, 1, 0 => (-2 : Int)
  | 0, 2, 0, 1, 1, 2 => (1 : Int)
  | 0, 2, 0, 1, 2, 1 => (1 : Int)
  | 0, 2, 0, 2, 1, 1 => (-2 : Int)
  | 0, 2, 0, 2, 3, 3 => (-2 : Int)
  | 0, 2, 0, 3, 2, 3 => (1 : Int)
  | 0, 2, 0, 3, 3, 2 => (1 : Int)
  | 0, 2, 1, 0, 1, 2 => (1 : Int)
  | 0, 2, 1, 0, 2, 1 => (1 : Int)
  | 0, 2, 1, 1, 0, 2 => (-2 : Int)
  | 0, 2, 1, 1, 2, 0 => (-2 : Int)
  | 0, 2, 1, 2, 0, 1 => (1 : Int)
  | 0, 2, 1, 2, 1, 0 => (1 : Int)
  | 0, 2, 2, 0, 1, 1 => (-2 : Int)
  | 0, 2, 2, 0, 3, 3 => (-2 : Int)
  | 0, 2, 2, 1, 0, 1 => (1 : Int)
  | 0, 2, 2, 1, 1, 0 => (1 : Int)
  | 0, 2, 2, 3, 0, 3 => (1 : Int)
  | 0, 2, 2, 3, 3, 0 => (1 : Int)
  | 0, 2, 3, 0, 2, 3 => (1 : Int)
  | 0, 2, 3, 0, 3, 2 => (1 : Int)
  | 0, 2, 3, 2, 0, 3 => (1 : Int)
  | 0, 2, 3, 2, 3, 0 => (1 : Int)
  | 0, 2, 3, 3, 0, 2 => (-2 : Int)
  | 0, 2, 3, 3, 2, 0 => (-2 : Int)
  | 0, 3, 0, 1, 1, 3 => (1 : Int)
  | 0, 3, 0, 1, 3, 1 => (1 : Int)
  | 0, 3, 0, 2, 2, 3 => (1 : Int)
  | 0, 3, 0, 2, 3, 2 => (1 : Int)
  | 0, 3, 0, 3, 1, 1 => (-2 : Int)
  | 0, 3, 0, 3, 2, 2 => (-2 : Int)
  | 0, 3, 1, 0, 1, 3 => (1 : Int)
  | 0, 3, 1, 0, 3, 1 => (1 : Int)
  | 0, 3, 1, 1, 0, 3 => (-2 : Int)
  | 0, 3, 1, 1, 3, 0 => (-2 : Int)
  | 0, 3, 1, 3, 0, 1 => (1 : Int)
  | 0, 3, 1, 3, 1, 0 => (1 : Int)
  | 0, 3, 2, 0, 2, 3 => (1 : Int)
  | 0, 3, 2, 0, 3, 2 => (1 : Int)
  | 0, 3, 2, 2, 0, 3 => (-2 : Int)
  | 0, 3, 2, 2, 3, 0 => (-2 : Int)
  | 0, 3, 2, 3, 0, 2 => (1 : Int)
  | 0, 3, 2, 3, 2, 0 => (1 : Int)
  | 0, 3, 3, 0, 1, 1 => (-2 : Int)
  | 0, 3, 3, 0, 2, 2 => (-2 : Int)
  | 0, 3, 3, 1, 0, 1 => (1 : Int)
  | 0, 3, 3, 1, 1, 0 => (1 : Int)
  | 0, 3, 3, 2, 0, 2 => (1 : Int)
  | 0, 3, 3, 2, 2, 0 => (1 : Int)
  | 1, 0, 0, 1, 2, 2 => (-2 : Int)
  | 1, 0, 0, 1, 3, 3 => (-2 : Int)
  | 1, 0, 0, 2, 1, 2 => (1 : Int)
  | 1, 0, 0, 2, 2, 1 => (1 : Int)
  | 1, 0, 0, 3, 1, 3 => (1 : Int)
  | 1, 0, 0, 3, 3, 1 => (1 : Int)
  | 1, 0, 1, 0, 2, 2 => (-2 : Int)
  | 1, 0, 1, 0, 3, 3 => (-2 : Int)
  | 1, 0, 1, 2, 0, 2 => (1 : Int)
  | 1, 0, 1, 2, 2, 0 => (1 : Int)
  | 1, 0, 1, 3, 0, 3 => (1 : Int)
  | 1, 0, 1, 3, 3, 0 => (1 : Int)
  | 1, 0, 2, 0, 1, 2 => (1 : Int)
  | 1, 0, 2, 0, 2, 1 => (1 : Int)
  | 1, 0, 2, 1, 0, 2 => (1 : Int)
  | 1, 0, 2, 1, 2, 0 => (1 : Int)
  | 1, 0, 2, 2, 0, 1 => (-2 : Int)
  | 1, 0, 2, 2, 1, 0 => (-2 : Int)
  | 1, 0, 3, 0, 1, 3 => (1 : Int)
  | 1, 0, 3, 0, 3, 1 => (1 : Int)
  | 1, 0, 3, 1, 0, 3 => (1 : Int)
  | 1, 0, 3, 1, 3, 0 => (1 : Int)
  | 1, 0, 3, 3, 0, 1 => (-2 : Int)
  | 1, 0, 3, 3, 1, 0 => (-2 : Int)
  | 1, 1, 0, 0, 2, 2 => (4 : Int)
  | 1, 1, 0, 0, 3, 3 => (4 : Int)
  | 1, 1, 0, 2, 0, 2 => (-2 : Int)
  | 1, 1, 0, 2, 2, 0 => (-2 : Int)
  | 1, 1, 0, 3, 0, 3 => (-2 : Int)
  | 1, 1, 0, 3, 3, 0 => (-2 : Int)
  | 1, 1, 2, 0, 0, 2 => (-2 : Int)
  | 1, 1, 2, 0, 2, 0 => (-2 : Int)
  | 1, 1, 2, 2, 0, 0 => (4 : Int)
  | 1, 1, 2, 2, 3, 3 => (4 : Int)
  | 1, 1, 2, 3, 2, 3 => (-2 : Int)
  | 1, 1, 2, 3, 3, 2 => (-2 : Int)
  | 1, 1, 3, 0, 0, 3 => (-2 : Int)
  | 1, 1, 3, 0, 3, 0 => (-2 : Int)
  | 1, 1, 3, 2, 2, 3 => (-2 : Int)
  | 1, 1, 3, 2, 3, 2 => (-2 : Int)
  | 1, 1, 3, 3, 0, 0 => (4 : Int)
  | 1, 1, 3, 3, 2, 2 => (4 : Int)
  | 1, 2, 0, 0, 1, 2 => (-2 : Int)
  | 1, 2, 0, 0, 2, 1 => (-2 : Int)
  | 1, 2, 0, 1, 0, 2 => (1 : Int)
  | 1, 2, 0, 1, 2, 0 => (1 : Int)
  | 1, 2, 0, 2, 0, 1 => (1 : Int)
  | 1, 2, 0, 2, 1, 0 => (1 : Int)
  | 1, 2, 1, 0, 0, 2 => (1 : Int)
  | 1, 2, 1, 0, 2, 0 => (1 : Int)
  | 1, 2, 1, 2, 0, 0 => (-2 : Int)
  | 1, 2, 1, 2, 3, 3 => (-2 : Int)
  | 1, 2, 1, 3, 2, 3 => (1 : Int)
  | 1, 2, 1, 3, 3, 2 => (1 : Int)
  | 1, 2, 2, 0, 0, 1 => (1 : Int)
  | 1, 2, 2, 0, 1, 0 => (1 : Int)
  | 1, 2, 2, 1, 0, 0 => (-2 : Int)
  | 1, 2, 2, 1, 3, 3 => (-2 : Int)
  | 1, 2, 2, 3, 1, 3 => (1 : Int)
  | 1, 2, 2, 3, 3, 1 => (1 : Int)
  | 1, 2, 3, 1, 2, 3 => (1 : Int)
  | 1, 2, 3, 1, 3, 2 => (1 : Int)
  | 1, 2, 3, 2, 1, 3 => (1 : Int)
  | 1, 2, 3, 2, 3, 1 => (1 : Int)
  | 1, 2, 3, 3, 1, 2 => (-2 : Int)
  | 1, 2, 3, 3, 2, 1 => (-2 : Int)
  | 1, 3, 0, 0, 1, 3 => (-2 : Int)
  | 1, 3, 0, 0, 3, 1 => (-2 : Int)
  | 1, 3, 0, 1, 0, 3 => (1 : Int)
  | 1, 3, 0, 1, 3, 0 => (1 : Int)
  | 1, 3, 0, 3, 0, 1 => (1 : Int)
  | 1, 3, 0, 3, 1, 0 => (1 : Int)
  | 1, 3, 1, 0, 0, 3 => (1 : Int)
  | 1, 3, 1, 0, 3, 0 => (1 : Int)
  | 1, 3, 1, 2, 2, 3 => (1 : Int)
  | 1, 3, 1, 2, 3, 2 => (1 : Int)
  | 1, 3, 1, 3, 0, 0 => (-2 : Int)
  | 1, 3, 1, 3, 2, 2 => (-2 : Int)
  | 1, 3, 2, 1, 2, 3 => (1 : Int)
  | 1, 3, 2, 1, 3, 2 => (1 : Int)
  | 1, 3, 2, 2, 1, 3 => (-2 : Int)
  | 1, 3, 2, 2, 3, 1 => (-2 : Int)
  | 1, 3, 2, 3, 1, 2 => (1 : Int)
  | 1, 3, 2, 3, 2, 1 => (1 : Int)
  | 1, 3, 3, 0, 0, 1 => (1 : Int)
  | 1, 3, 3, 0, 1, 0 => (1 : Int)
  | 1, 3, 3, 1, 0, 0 => (-2 : Int)
  | 1, 3, 3, 1, 2, 2 => (-2 : Int)
  | 1, 3, 3, 2, 1, 2 => (1 : Int)
  | 1, 3, 3, 2, 2, 1 => (1 : Int)
  | 2, 0, 0, 1, 1, 2 => (1 : Int)
  | 2, 0, 0, 1, 2, 1 => (1 : Int)
  | 2, 0, 0, 2, 1, 1 => (-2 : Int)
  | 2, 0, 0, 2, 3, 3 => (-2 : Int)
  | 2, 0, 0, 3, 2, 3 => (1 : Int)
  | 2, 0, 0, 3, 3, 2 => (1 : Int)
  | 2, 0, 1, 0, 1, 2 => (1 : Int)
  | 2, 0, 1, 0, 2, 1 => (1 : Int)
  | 2, 0, 1, 1, 0, 2 => (-2 : Int)
  | 2, 0, 1, 1, 2, 0 => (-2 : Int)
  | 2, 0, 1, 2, 0, 1 => (1 : Int)
  | 2, 0, 1, 2, 1, 0 => (1 : Int)
  | 2, 0, 2, 0, 1, 1 => (-2 : Int)
  | 2, 0, 2, 0, 3, 3 => (-2 : Int)
  | 2, 0, 2, 1, 0, 1 => (1 : Int)
  | 2, 0, 2, 1, 1, 0 => (1 : Int)
  | 2, 0, 2, 3, 0, 3 => (1 : Int)
  | 2, 0, 2, 3, 3, 0 => (1 : Int)
  | 2, 0, 3, 0, 2, 3 => (1 : Int)
  | 2, 0, 3, 0, 3, 2 => (1 : Int)
  | 2, 0, 3, 2, 0, 3 => (1 : Int)
  | 2, 0, 3, 2, 3, 0 => (1 : Int)
  | 2, 0, 3, 3, 0, 2 => (-2 : Int)
  | 2, 0, 3, 3, 2, 0 => (-2 : Int)
  | 2, 1, 0, 0, 1, 2 => (-2 : Int)
  | 2, 1, 0, 0, 2, 1 => (-2 : Int)
  | 2, 1, 0, 1, 0, 2 => (1 : Int)
  | 2, 1, 0, 1, 2, 0 => (1 : Int)
  | 2, 1, 0, 2, 0, 1 => (1 : Int)
  | 2, 1, 0, 2, 1, 0 => (1 : Int)
  | 2, 1, 1, 0, 0, 2 => (1 : Int)
  | 2, 1, 1, 0, 2, 0 => (1 : Int)
  | 2, 1, 1, 2, 0, 0 => (-2 : Int)
  | 2, 1, 1, 2, 3, 3 => (-2 : Int)
  | 2, 1, 1, 3, 2, 3 => (1 : Int)
  | 2, 1, 1, 3, 3, 2 => (1 : Int)
  | 2, 1, 2, 0, 0, 1 => (1 : Int)
  | 2, 1, 2, 0, 1, 0 => (1 : Int)
  | 2, 1, 2, 1, 0, 0 => (-2 : Int)
  | 2, 1, 2, 1, 3, 3 => (-2 : Int)
  | 2, 1, 2, 3, 1, 3 => (1 : Int)
  | 2, 1, 2, 3, 3, 1 => (1 : Int)
  | 2, 1, 3, 1, 2, 3 => (1 : Int)
  | 2, 1, 3, 1, 3, 2 => (1 : Int)
  | 2, 1, 3, 2, 1, 3 => (1 : Int)
  | 2, 1, 3, 2, 3, 1 => (1 : Int)
  | 2, 1, 3, 3, 1, 2 => (-2 : Int)
  | 2, 1, 3, 3, 2, 1 => (-2 : Int)
  | 2, 2, 0, 0, 1, 1 => (4 : Int)
  | 2, 2, 0, 0, 3, 3 => (4 : Int)
  | 2, 2, 0, 1, 0, 1 => (-2 : Int)
  | 2, 2, 0, 1, 1, 0 => (-2 : Int)
  | 2, 2, 0, 3, 0, 3 => (-2 : Int)
  | 2, 2, 0, 3, 3, 0 => (-2 : Int)
  | 2, 2, 1, 0, 0, 1 => (-2 : Int)
  | 2, 2, 1, 0, 1, 0 => (-2 : Int)
  | 2, 2, 1, 1, 0, 0 => (4 : Int)
  | 2, 2, 1, 1, 3, 3 => (4 : Int)
  | 2, 2, 1, 3, 1, 3 => (-2 : Int)
  | 2, 2, 1, 3, 3, 1 => (-2 : Int)
  | 2, 2, 3, 0, 0, 3 => (-2 : Int)
  | 2, 2, 3, 0, 3, 0 => (-2 : Int)
  | 2, 2, 3, 1, 1, 3 => (-2 : Int)
  | 2, 2, 3, 1, 3, 1 => (-2 : Int)
  | 2, 2, 3, 3, 0, 0 => (4 : Int)
  | 2, 2, 3, 3, 1, 1 => (4 : Int)
  | 2, 3, 0, 0, 2, 3 => (-2 : Int)
  | 2, 3, 0, 0, 3, 2 => (-2 : Int)
  | 2, 3, 0, 2, 0, 3 => (1 : Int)
  | 2, 3, 0, 2, 3, 0 => (1 : Int)
  | 2, 3, 0, 3, 0, 2 => (1 : Int)
  | 2, 3, 0, 3, 2, 0 => (1 : Int)
  | 2, 3, 1, 1, 2, 3 => (-2 : Int)
  | 2, 3, 1, 1, 3, 2 => (-2 : Int)
  | 2, 3, 1, 2, 1, 3 => (1 : Int)
  | 2, 3, 1, 2, 3, 1 => (1 : Int)
  | 2, 3, 1, 3, 1, 2 => (1 : Int)
  | 2, 3, 1, 3, 2, 1 => (1 : Int)
  | 2, 3, 2, 0, 0, 3 => (1 : Int)
  | 2, 3, 2, 0, 3, 0 => (1 : Int)
  | 2, 3, 2, 1, 1, 3 => (1 : Int)
  | 2, 3, 2, 1, 3, 1 => (1 : Int)
  | 2, 3, 2, 3, 0, 0 => (-2 : Int)
  | 2, 3, 2, 3, 1, 1 => (-2 : Int)
  | 2, 3, 3, 0, 0, 2 => (1 : Int)
  | 2, 3, 3, 0, 2, 0 => (1 : Int)
  | 2, 3, 3, 1, 1, 2 => (1 : Int)
  | 2, 3, 3, 1, 2, 1 => (1 : Int)
  | 2, 3, 3, 2, 0, 0 => (-2 : Int)
  | 2, 3, 3, 2, 1, 1 => (-2 : Int)
  | 3, 0, 0, 1, 1, 3 => (1 : Int)
  | 3, 0, 0, 1, 3, 1 => (1 : Int)
  | 3, 0, 0, 2, 2, 3 => (1 : Int)
  | 3, 0, 0, 2, 3, 2 => (1 : Int)
  | 3, 0, 0, 3, 1, 1 => (-2 : Int)
  | 3, 0, 0, 3, 2, 2 => (-2 : Int)
  | 3, 0, 1, 0, 1, 3 => (1 : Int)
  | 3, 0, 1, 0, 3, 1 => (1 : Int)
  | 3, 0, 1, 1, 0, 3 => (-2 : Int)
  | 3, 0, 1, 1, 3, 0 => (-2 : Int)
  | 3, 0, 1, 3, 0, 1 => (1 : Int)
  | 3, 0, 1, 3, 1, 0 => (1 : Int)
  | 3, 0, 2, 0, 2, 3 => (1 : Int)
  | 3, 0, 2, 0, 3, 2 => (1 : Int)
  | 3, 0, 2, 2, 0, 3 => (-2 : Int)
  | 3, 0, 2, 2, 3, 0 => (-2 : Int)
  | 3, 0, 2, 3, 0, 2 => (1 : Int)
  | 3, 0, 2, 3, 2, 0 => (1 : Int)
  | 3, 0, 3, 0, 1, 1 => (-2 : Int)
  | 3, 0, 3, 0, 2, 2 => (-2 : Int)
  | 3, 0, 3, 1, 0, 1 => (1 : Int)
  | 3, 0, 3, 1, 1, 0 => (1 : Int)
  | 3, 0, 3, 2, 0, 2 => (1 : Int)
  | 3, 0, 3, 2, 2, 0 => (1 : Int)
  | 3, 1, 0, 0, 1, 3 => (-2 : Int)
  | 3, 1, 0, 0, 3, 1 => (-2 : Int)
  | 3, 1, 0, 1, 0, 3 => (1 : Int)
  | 3, 1, 0, 1, 3, 0 => (1 : Int)
  | 3, 1, 0, 3, 0, 1 => (1 : Int)
  | 3, 1, 0, 3, 1, 0 => (1 : Int)
  | 3, 1, 1, 0, 0, 3 => (1 : Int)
  | 3, 1, 1, 0, 3, 0 => (1 : Int)
  | 3, 1, 1, 2, 2, 3 => (1 : Int)
  | 3, 1, 1, 2, 3, 2 => (1 : Int)
  | 3, 1, 1, 3, 0, 0 => (-2 : Int)
  | 3, 1, 1, 3, 2, 2 => (-2 : Int)
  | 3, 1, 2, 1, 2, 3 => (1 : Int)
  | 3, 1, 2, 1, 3, 2 => (1 : Int)
  | 3, 1, 2, 2, 1, 3 => (-2 : Int)
  | 3, 1, 2, 2, 3, 1 => (-2 : Int)
  | 3, 1, 2, 3, 1, 2 => (1 : Int)
  | 3, 1, 2, 3, 2, 1 => (1 : Int)
  | 3, 1, 3, 0, 0, 1 => (1 : Int)
  | 3, 1, 3, 0, 1, 0 => (1 : Int)
  | 3, 1, 3, 1, 0, 0 => (-2 : Int)
  | 3, 1, 3, 1, 2, 2 => (-2 : Int)
  | 3, 1, 3, 2, 1, 2 => (1 : Int)
  | 3, 1, 3, 2, 2, 1 => (1 : Int)
  | 3, 2, 0, 0, 2, 3 => (-2 : Int)
  | 3, 2, 0, 0, 3, 2 => (-2 : Int)
  | 3, 2, 0, 2, 0, 3 => (1 : Int)
  | 3, 2, 0, 2, 3, 0 => (1 : Int)
  | 3, 2, 0, 3, 0, 2 => (1 : Int)
  | 3, 2, 0, 3, 2, 0 => (1 : Int)
  | 3, 2, 1, 1, 2, 3 => (-2 : Int)
  | 3, 2, 1, 1, 3, 2 => (-2 : Int)
  | 3, 2, 1, 2, 1, 3 => (1 : Int)
  | 3, 2, 1, 2, 3, 1 => (1 : Int)
  | 3, 2, 1, 3, 1, 2 => (1 : Int)
  | 3, 2, 1, 3, 2, 1 => (1 : Int)
  | 3, 2, 2, 0, 0, 3 => (1 : Int)
  | 3, 2, 2, 0, 3, 0 => (1 : Int)
  | 3, 2, 2, 1, 1, 3 => (1 : Int)
  | 3, 2, 2, 1, 3, 1 => (1 : Int)
  | 3, 2, 2, 3, 0, 0 => (-2 : Int)
  | 3, 2, 2, 3, 1, 1 => (-2 : Int)
  | 3, 2, 3, 0, 0, 2 => (1 : Int)
  | 3, 2, 3, 0, 2, 0 => (1 : Int)
  | 3, 2, 3, 1, 1, 2 => (1 : Int)
  | 3, 2, 3, 1, 2, 1 => (1 : Int)
  | 3, 2, 3, 2, 0, 0 => (-2 : Int)
  | 3, 2, 3, 2, 1, 1 => (-2 : Int)
  | 3, 3, 0, 0, 1, 1 => (4 : Int)
  | 3, 3, 0, 0, 2, 2 => (4 : Int)
  | 3, 3, 0, 1, 0, 1 => (-2 : Int)
  | 3, 3, 0, 1, 1, 0 => (-2 : Int)
  | 3, 3, 0, 2, 0, 2 => (-2 : Int)
  | 3, 3, 0, 2, 2, 0 => (-2 : Int)
  | 3, 3, 1, 0, 0, 1 => (-2 : Int)
  | 3, 3, 1, 0, 1, 0 => (-2 : Int)
  | 3, 3, 1, 1, 0, 0 => (4 : Int)
  | 3, 3, 1, 1, 2, 2 => (4 : Int)
  | 3, 3, 1, 2, 1, 2 => (-2 : Int)
  | 3, 3, 1, 2, 2, 1 => (-2 : Int)
  | 3, 3, 2, 0, 0, 2 => (-2 : Int)
  | 3, 3, 2, 0, 2, 0 => (-2 : Int)
  | 3, 3, 2, 1, 1, 2 => (-2 : Int)
  | 3, 3, 2, 1, 2, 1 => (-2 : Int)
  | 3, 3, 2, 2, 0, 0 => (4 : Int)
  | 3, 3, 2, 2, 1, 1 => (4 : Int)
  | _, _, _, _, _, _ => (0 : Int)

def closedZ (a b c d i j : Fin 4) : Int :=
  (if a = c ∧ b = d ∧ i = j then (-4 : Int) else 0) +
    (if a = c ∧ b = i ∧ d = j then (8 : Int) else 0) +
    (if a = b ∧ c = d ∧ i = j then (4 : Int) else 0) +
    (if a = b ∧ c = i ∧ d = j then (-8 : Int) else 0)

def sym4Z (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int)
    (a b c d i j : Fin 4) : Int :=
  (C a b c d i j + C b a c d i j + C a b d c i j + C b a d c i j) / 4

def symFullZ (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → Int)
    (a b c d i j : Fin 4) : Int :=
  (sym4Z C a b c d i j + sym4Z C c d a b i j) / 2

theorem symFullZ_explicit_eq_closed :
    ∀ a b c d i j : Fin 4,
      symFullZ explicitZ a b c d i j = symFullZ closedZ a b c d i j := by
  decide

end KernelCert
end ReggeExactMidpointM2TTIdentity4D
end Analysis
end Gravity
end IndisputableMonolith
