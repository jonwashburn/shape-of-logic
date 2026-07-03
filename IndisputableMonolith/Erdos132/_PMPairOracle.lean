/-
  Erdos132 pm-pair certificate ORACLE (auto-generated; do not hand-edit).
  Source: scripts/erdos132/_pmpair_oracle_lean_gen.py from _pmpair_oracle.json.

  Interface lock for the division-free Positivstellensatz pm-pair route.
  Every one of the 118 pm-pair infeasibility cores reduces to a sign-definite AFFINE
  edge L(a,b) = ca*a + cb*b + c0 that the core forces to 0, while the box bounds
  0 < a, 0 < b (a = u^2, b = v^2) force L strictly positive on the open square.
  Refutation is `linarith` from the box bounds: no nlinarith, no division, no SOS.

  MEASURED: all 118 cores collapse to exactly two edges, L = a and L = b, i.e. every
  pm-pair core forces u^2 = 0 or v^2 = 0. Sound because 0 < u, v.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace Erdos132.PMPairOracle

/-- An affine edge `ca*a + cb*b + c0` over the recognition box, stored by its
rational coefficients (the "edge label" Lean recomputes from). -/
structure Edge where
  ca : ℚ
  cb : ℚ
  c0 : ℚ
  deriving DecidableEq

/-- Recompute the edge value from its stored coefficients. -/
def evalEdge (e : Edge) (a b : ℝ) : ℝ := (e.ca : ℝ) * a + (e.cb : ℝ) * b + (e.c0 : ℝ)

/-- The full 118-core pm-pair dispatch table (auto-generated, one entry per core).
This is the DATA that documents every core; the oracle below proves False for any
edge in the (deduplicated) support of this table. -/
def coreEdges : List Edge := [
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 0: combo 012345 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 1: combo 012346 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 2: combo 012347 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 3: combo 012348 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 4: combo 012349 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 5: combo 0123412 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 6: combo 0123413 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 7: combo 0123416 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 8: combo 0123417 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 9: combo 012367 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 10: combo 012368 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 11: combo 012369 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 12: combo 0123612 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 13: combo 0123613 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 14: combo 012389 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 15: combo 0123812 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 16: combo 0123813 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 17: combo 01231213 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 18: combo 01231216 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 19: combo 01231217 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 20: combo 01231617 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 21: combo 0124612 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 22: combo 0124613 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 23: combo 0124713 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 24: combo 012489 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 25: combo 012589 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 26: combo 012689 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 27: combo 012789 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 28: combo 0128912 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 29: combo 0128913 pmpair (0, 1, 2) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 30: combo 01891011 pmpair (0, 1, 4) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 31: combo 01891014 pmpair (0, 1, 4) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 32: combo 01891015 pmpair (0, 1, 4) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 33: combo 01891016 pmpair (0, 1, 4) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 34: combo 01891017 pmpair (0, 1, 4) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 35: combo 018101114 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 36: combo 018101115 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 37: combo 018101116 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 38: combo 018101117 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 39: combo 018101416 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 40: combo 018101417 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 41: combo 018101517 pmpair (0, 1, 3) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 42: combo 0110111415 pmpair (0, 1, 2) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 43: combo 023456 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 44: combo 023457 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 45: combo 023458 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 46: combo 023459 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 47: combo 0234510 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 48: combo 0234511 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 49: combo 023467 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 50: combo 0234612 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 51: combo 0234613 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 52: combo 0234614 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 53: combo 0234615 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 54: combo 0234713 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 55: combo 0234715 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 56: combo 023489 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 57: combo 0234810 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 58: combo 0234811 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 59: combo 0234812 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 60: combo 0234813 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 61: combo 0234814 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 62: combo 0234815 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 63: combo 0234911 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 64: combo 0234913 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 65: combo 0234915 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 66: combo 02341213 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 67: combo 02341214 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 68: combo 02341215 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 69: combo 02341216 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 70: combo 02341217 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 71: combo 02341315 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 72: combo 02341317 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 73: combo 02341416 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 74: combo 02341417 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 75: combo 02341517 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 76: combo 023567 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 77: combo 023589 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 78: combo 02351213 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 79: combo 023678 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 80: combo 023679 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 81: combo 0236710 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 82: combo 0236711 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 83: combo 023689 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 84: combo 0236810 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 85: combo 0236811 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 86: combo 0236812 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 87: combo 0236813 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 88: combo 0236814 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 89: combo 0236815 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 90: combo 0236911 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 91: combo 0236913 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 92: combo 0236915 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 93: combo 02361214 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 94: combo 02361215 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 95: combo 02361315 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 96: combo 023789 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 97: combo 0238912 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 98: combo 0238913 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 99: combo 02381213 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 100: combo 02381214 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 101: combo 02381215 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 102: combo 02381315 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 103: combo 02391213 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 104: combo 023121314 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 105: combo 023121315 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 106: combo 023121416 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 107: combo 023121417 pmpair (1, 2, 0) edge eq1
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,  -- core 108: combo 023121517 pmpair (1, 2, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 109: combo 089101114 pmpair (3, 4, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 110: combo 089101115 pmpair (3, 4, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 111: combo 089101116 pmpair (3, 4, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 112: combo 089101117 pmpair (3, 4, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 113: combo 0810111415 pmpair (2, 3, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 114: combo 0810111416 pmpair (2, 3, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 115: combo 0810111417 pmpair (2, 3, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩,  -- core 116: combo 0810111517 pmpair (2, 3, 0) edge eq1
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩  -- core 117: combo 0910111415 pmpair (2, 3, 0) edge eq1
]

/-- The distinct edges appearing across all 118 cores. MEASURED: exactly 2
of them (`a` and `b`). -/
def distinctEdges : List Edge := [
  ⟨(1 : ℚ), (0 : ℚ), (0 : ℚ)⟩,
  ⟨(0 : ℚ), (1 : ℚ), (0 : ℚ)⟩
]

/-- **The pm-pair oracle.** Any edge that appears in a pm-pair core, when forced to
zero, contradicts the box bounds `0 < a, 0 < b` (a = u^2, b = v^2). Proved by
exhausting the 2 distinct edges and `linarith` on each recomputed edge value.
No nlinarith, no division, no SOS. -/
theorem refute_pmpair_edge (e : Edge) (he : e ∈ distinctEdges) (a b : ℝ)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (hE : evalEdge e a b = 0) : False := by
  fin_cases he <;>
    · simp only [evalEdge, Rat.cast_zero, Rat.cast_one, zero_mul, one_mul,
        add_zero, zero_add] at hE
      linarith

/-- Every core's edge is one of the distinct edges (scale check: the 118-entry
table has support exactly `distinctEdges`). -/
theorem coreEdges_support : ∀ e ∈ coreEdges, e ∈ distinctEdges := by
  intro e he
  fin_cases he <;> decide

/-- **Full-scale corollary.** For every one of the 118 pm-pair cores, its edge
forced to zero contradicts the box bounds. This is the oracle applied across the
entire core set via the support lemma. -/
theorem refute_pmpair_core (e : Edge) (he : e ∈ coreEdges) (a b : ℝ)
    (ha0 : 0 < a) (hb0 : 0 < b)
    (hE : evalEdge e a b = 0) : False :=
  refute_pmpair_edge e (coreEdges_support e he) a b ha0 hb0 hE

/-! ### Coefficient-sensitivity negative control.
A corrupted edge that is NOT sign-definite on the open square (has an interior
zero) is genuinely NOT refutable from the box bounds. We prove the discriminator:
the corrupt edge `a - 1/2` vanishes at the interior point `a = 1/2`, so no oracle
lemma could close it. This documents that the refutation depends on the edge being
sign-definite, not on any vacuous pattern. -/
example : evalEdge ⟨(1 : ℚ), (0 : ℚ), (-1 / 2 : ℚ)⟩ (1 / 2) (1 / 2) = 0 := by
  simp [evalEdge]; norm_num

-- Axiom audit: must be exactly [propext, Classical.choice, Quot.sound].
#print axioms refute_pmpair_core

end Erdos132.PMPairOracle
