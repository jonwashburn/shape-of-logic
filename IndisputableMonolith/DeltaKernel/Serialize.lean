import IndisputableMonolith.DeltaKernel.Syntax
import IndisputableMonolith.DeltaKernel.Ledger
import IndisputableMonolith.DeltaKernel.Check

/-!
# δ-Kernel: Serialization (the Phase-2 wire format)

S-expression codec for `DTerm`, `DFormula`, `Deriv`, `Ledger`, contexts,
and check verdicts. This is what makes the kernel EXTRACTABLE: a standalone
binary (`deltak`, see `Main.lean`) reads a derivation off the wire, runs the
same `check` function the soundness theorem is about, and prints the verdict.

Trust architecture (panel Phase 2: extracted binary, differentially
validated against the Lean-hosted version, never a from-scratch prover):

1. **Sexp layer, PROVED.** `fromSexp (toSexp x) = some x` is a theorem for
   every codec in this file, checked by Lean's kernel by structural
   induction over ALL terms/formulas/derivations, not spot-checked on
   examples. The wire format cannot silently drop or permute a rule.
2. **String layer, MEASURED.** `Sexp.parse (Sexp.print e) = some e` is
   validated empirically by the binary's `selftest` over the bundled
   corpus (and by the differential harness), not proved in general.
   Parser correctness as a theorem is pre-registered future work.
3. **Compiled layer, DIFFERENTIAL.** The binary re-evaluates `check` with
   the compiler and compares against verdicts the kernel certified by
   `decide` (see `Main.lean`'s `corpus_matches`). A compiler/kernel
   disagreement fails the harness.

Numerals on the wire are UNARY (`z`, `(s n)`): de Bruijn indices in real
derivations are tiny, the object language's numerals are already
succ-chains, and the unary codec's round-trip is a two-line induction
instead of a decimal-digits lemma stack. A decimal atom codec is a
compatibility refinement, not a foundational need.

No Mathlib. Imports nothing beyond the kernel's own modules.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-! ## S-expressions -/

/-- S-expressions: atoms and nodes. The whole wire format. -/
inductive Sexp : Type where
  | atom : String → Sexp
  | node : List Sexp → Sexp
deriving Repr

namespace Sexp

mutual

/-- Structural equality (deriving cannot handle the nested `List Sexp`). -/
def beq : Sexp → Sexp → Bool
  | .atom a, .atom b => a == b
  | .node es, .node fs => beqList es fs
  | _, _ => false

/-- Structural equality on lists of S-expressions. -/
def beqList : List Sexp → List Sexp → Bool
  | [], [] => true
  | e :: es, f :: fs => beq e f && beqList es fs
  | _, _ => false

end

instance : BEq Sexp := ⟨beq⟩

mutual

/-- Print an S-expression. Atoms must not contain whitespace or parens;
every atom this module emits is a bare tag (`var`, `s`, `z`, ...). -/
def print : Sexp → String
  | .atom a => a
  | .node es => "(" ++ printList es ++ ")"

/-- Print a list of S-expressions, space-separated. -/
def printList : List Sexp → String
  | [] => ""
  | [e] => print e
  | e :: es => print e ++ " " ++ printList es

end

/-- Flush the current atom accumulator into the token list. -/
private def flushTok (cur : List Char) (acc : List String) : List String :=
  if cur.isEmpty then acc else String.ofList cur.reverse :: acc

/-- Tokenizer: parens are their own tokens; whitespace separates atoms. -/
private def tokenizeAux : List Char → List Char → List String → List String
  | [], cur, acc => (flushTok cur acc).reverse
  | c :: cs, cur, acc =>
    if c = '(' then tokenizeAux cs [] ("(" :: flushTok cur acc)
    else if c = ')' then tokenizeAux cs [] (")" :: flushTok cur acc)
    else if c = ' ' ∨ c = '\n' ∨ c = '\t' ∨ c = '\r' then
      tokenizeAux cs [] (flushTok cur acc)
    else tokenizeAux cs (c :: cur) acc

/-- Tokenize a string into parens and atoms. -/
def tokenize (s : String) : List String := tokenizeAux s.toList [] []

mutual

/-- Parse one S-expression from a token stream (fuel-bounded recursive
descent; the fuel argument makes totality structural). -/
def parseOne : Nat → List String → Option (Sexp × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: ts =>
    if t = "(" then
      match parseMany fuel ts with
      | some (es, ")" :: rest) => some (.node es, rest)
      | _ => none
    else if t = ")" then none
    else some (.atom t, ts)

/-- Parse a list of S-expressions up to a closing paren or end of input. -/
def parseMany : Nat → List String → Option (List Sexp × List String)
  | 0, _ => none
  | fuel + 1, ts =>
    match ts with
    | [] => some ([], [])
    | ")" :: _ => some ([], ts)
    | _ =>
      match parseOne fuel ts with
      | some (e, rest) =>
        match parseMany fuel rest with
        | some (es, rest') => some (e :: es, rest')
        | none => none
      | none => none

end

/-- Parse a complete S-expression (the whole input must be consumed). -/
def parse (s : String) : Option Sexp :=
  let toks := tokenize s
  match parseOne (toks.length + 1) toks with
  | some (e, []) => some e
  | _ => none

end Sexp

/-! ## Unary numerals -/

/-- Encode a natural as a unary S-expression: `z`, `(s z)`, `(s (s z))`, ... -/
def natToSexp : Nat → Sexp
  | 0 => .atom "z"
  | n + 1 => .node [.atom "s", natToSexp n]

/-- Decode a unary numeral. -/
def natFromSexp : Sexp → Option Nat
  | .atom "z" => some 0
  | .node [.atom "s", e] =>
    match natFromSexp e with
    | some n => some (n + 1)
    | none => none
  | _ => none

theorem natFromSexp_toSexp (n : Nat) : natFromSexp (natToSexp n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natToSexp, natFromSexp, ih]

/-! ## Booleans -/

/-- Encode a boolean as `t` / `f`. -/
def boolToSexp : Bool → Sexp
  | true => .atom "t"
  | false => .atom "f"

/-- Decode a boolean. -/
def boolFromSexp : Sexp → Option Bool
  | .atom "t" => some true
  | .atom "f" => some false
  | _ => none

theorem boolFromSexp_toSexp (b : Bool) : boolFromSexp (boolToSexp b) = some b := by
  cases b <;> rfl

/-! ## Terms -/

namespace DTerm

/-- Encode a δ-term. -/
def toSexp : DTerm → Sexp
  | .var n => .node [.atom "var", natToSexp n]
  | .zero => .atom "zero"
  | .succ t => .node [.atom "succ", t.toSexp]
  | .add t s => .node [.atom "add", t.toSexp, s.toSexp]
  | .mul t s => .node [.atom "mul", t.toSexp, s.toSexp]

/-- Decode a δ-term. -/
def fromSexp : Sexp → Option DTerm
  | .node [.atom "var", n] =>
    match natFromSexp n with
    | some n => some (.var n)
    | none => none
  | .atom "zero" => some .zero
  | .node [.atom "succ", t] =>
    match fromSexp t with
    | some t => some (.succ t)
    | none => none
  | .node [.atom "add", t, s] =>
    match fromSexp t, fromSexp s with
    | some t, some s => some (.add t s)
    | _, _ => none
  | .node [.atom "mul", t, s] =>
    match fromSexp t, fromSexp s with
    | some t, some s => some (.mul t s)
    | _, _ => none
  | _ => none

/-- The term codec is lossless: proved for ALL terms by induction, not
spot-checked. -/
theorem fromSexp_toSexp (t : DTerm) : fromSexp t.toSexp = some t := by
  induction t <;> simp [toSexp, fromSexp, natFromSexp_toSexp, *]

end DTerm

/-! ## Formulas -/

namespace DFormula

/-- Encode a δ-formula. -/
def toSexp : DFormula → Sexp
  | .eq t s => .node [.atom "eq", t.toSexp, s.toSexp]
  | .fls => .atom "fls"
  | .conj a b => .node [.atom "conj", a.toSexp, b.toSexp]
  | .disj a b => .node [.atom "disj", a.toSexp, b.toSexp]
  | .impl a b => .node [.atom "impl", a.toSexp, b.toSexp]
  | .all a => .node [.atom "all", a.toSexp]
  | .ex a => .node [.atom "ex", a.toSexp]

/-- Decode a δ-formula. -/
def fromSexp : Sexp → Option DFormula
  | .node [.atom "eq", t, s] =>
    match DTerm.fromSexp t, DTerm.fromSexp s with
    | some t, some s => some (.eq t s)
    | _, _ => none
  | .atom "fls" => some .fls
  | .node [.atom "conj", a, b] =>
    match fromSexp a, fromSexp b with
    | some a, some b => some (.conj a b)
    | _, _ => none
  | .node [.atom "disj", a, b] =>
    match fromSexp a, fromSexp b with
    | some a, some b => some (.disj a b)
    | _, _ => none
  | .node [.atom "impl", a, b] =>
    match fromSexp a, fromSexp b with
    | some a, some b => some (.impl a b)
    | _, _ => none
  | .node [.atom "all", a] =>
    match fromSexp a with
    | some a => some (.all a)
    | none => none
  | .node [.atom "ex", a] =>
    match fromSexp a with
    | some a => some (.ex a)
    | none => none
  | _ => none

/-- The formula codec is lossless: proved for ALL formulas by induction. -/
theorem fromSexp_toSexp (φ : DFormula) : fromSexp φ.toSexp = some φ := by
  induction φ <;> simp [toSexp, fromSexp, DTerm.fromSexp_toSexp, *]

end DFormula

/-! ## Derivations -/

namespace Deriv

/-- Encode a derivation tree. One tag per rule; the tag set IS the rule
inventory, so a wire-level grep for `emPosit`/`lpoPosit`/`mpPosit`/`ind`
is the same oracle-symbol audit `Sigma.lean` performs on the tree. -/
def toSexp : Deriv → Sexp
  | .hyp i => .node [.atom "hyp", natToSexp i]
  | .eqRefl t => .node [.atom "eqRefl", t.toSexp]
  | .eqSubst φ t s d₁ d₂ =>
      .node [.atom "eqSubst", φ.toSexp, t.toSexp, s.toSexp, d₁.toSexp, d₂.toSexp]
  | .succNeZero t => .node [.atom "succNeZero", t.toSexp]
  | .succInj d => .node [.atom "succInj", d.toSexp]
  | .addZero t => .node [.atom "addZero", t.toSexp]
  | .addSucc t s => .node [.atom "addSucc", t.toSexp, s.toSexp]
  | .mulZero t => .node [.atom "mulZero", t.toSexp]
  | .mulSucc t s => .node [.atom "mulSucc", t.toSexp, s.toSexp]
  | .ind φ d₀ dS => .node [.atom "ind", φ.toSexp, d₀.toSexp, dS.toSexp]
  | .implIntro φ d => .node [.atom "implIntro", φ.toSexp, d.toSexp]
  | .implElim d₁ d₂ => .node [.atom "implElim", d₁.toSexp, d₂.toSexp]
  | .conjIntro d₁ d₂ => .node [.atom "conjIntro", d₁.toSexp, d₂.toSexp]
  | .conjElim1 d => .node [.atom "conjElim1", d.toSexp]
  | .conjElim2 d => .node [.atom "conjElim2", d.toSexp]
  | .disjIntro1 ψ d => .node [.atom "disjIntro1", ψ.toSexp, d.toSexp]
  | .disjIntro2 φ d => .node [.atom "disjIntro2", φ.toSexp, d.toSexp]
  | .disjElim d dL dR => .node [.atom "disjElim", d.toSexp, dL.toSexp, dR.toSexp]
  | .flsElim φ d => .node [.atom "flsElim", φ.toSexp, d.toSexp]
  | .allIntro d => .node [.atom "allIntro", d.toSexp]
  | .allElim t d => .node [.atom "allElim", t.toSexp, d.toSexp]
  | .exIntro φ t d => .node [.atom "exIntro", φ.toSexp, t.toSexp, d.toSexp]
  | .exElim ψ d dBody => .node [.atom "exElim", ψ.toSexp, d.toSexp, dBody.toSexp]
  | .emPosit φ => .node [.atom "emPosit", φ.toSexp]
  | .lpoPosit φ => .node [.atom "lpoPosit", φ.toSexp]
  | .mpPosit φ => .node [.atom "mpPosit", φ.toSexp]

/-- Decode a derivation tree. -/
def fromSexp : Sexp → Option Deriv
  | .node [.atom "hyp", i] =>
    match natFromSexp i with
    | some i => some (.hyp i)
    | none => none
  | .node [.atom "eqRefl", t] =>
    match DTerm.fromSexp t with
    | some t => some (.eqRefl t)
    | none => none
  | .node [.atom "eqSubst", φ, t, s, d₁, d₂] =>
    match DFormula.fromSexp φ, DTerm.fromSexp t, DTerm.fromSexp s,
          fromSexp d₁, fromSexp d₂ with
    | some φ, some t, some s, some d₁, some d₂ => some (.eqSubst φ t s d₁ d₂)
    | _, _, _, _, _ => none
  | .node [.atom "succNeZero", t] =>
    match DTerm.fromSexp t with
    | some t => some (.succNeZero t)
    | none => none
  | .node [.atom "succInj", d] =>
    match fromSexp d with
    | some d => some (.succInj d)
    | none => none
  | .node [.atom "addZero", t] =>
    match DTerm.fromSexp t with
    | some t => some (.addZero t)
    | none => none
  | .node [.atom "addSucc", t, s] =>
    match DTerm.fromSexp t, DTerm.fromSexp s with
    | some t, some s => some (.addSucc t s)
    | _, _ => none
  | .node [.atom "mulZero", t] =>
    match DTerm.fromSexp t with
    | some t => some (.mulZero t)
    | none => none
  | .node [.atom "mulSucc", t, s] =>
    match DTerm.fromSexp t, DTerm.fromSexp s with
    | some t, some s => some (.mulSucc t s)
    | _, _ => none
  | .node [.atom "ind", φ, d₀, dS] =>
    match DFormula.fromSexp φ, fromSexp d₀, fromSexp dS with
    | some φ, some d₀, some dS => some (.ind φ d₀ dS)
    | _, _, _ => none
  | .node [.atom "implIntro", φ, d] =>
    match DFormula.fromSexp φ, fromSexp d with
    | some φ, some d => some (.implIntro φ d)
    | _, _ => none
  | .node [.atom "implElim", d₁, d₂] =>
    match fromSexp d₁, fromSexp d₂ with
    | some d₁, some d₂ => some (.implElim d₁ d₂)
    | _, _ => none
  | .node [.atom "conjIntro", d₁, d₂] =>
    match fromSexp d₁, fromSexp d₂ with
    | some d₁, some d₂ => some (.conjIntro d₁ d₂)
    | _, _ => none
  | .node [.atom "conjElim1", d] =>
    match fromSexp d with
    | some d => some (.conjElim1 d)
    | none => none
  | .node [.atom "conjElim2", d] =>
    match fromSexp d with
    | some d => some (.conjElim2 d)
    | none => none
  | .node [.atom "disjIntro1", ψ, d] =>
    match DFormula.fromSexp ψ, fromSexp d with
    | some ψ, some d => some (.disjIntro1 ψ d)
    | _, _ => none
  | .node [.atom "disjIntro2", φ, d] =>
    match DFormula.fromSexp φ, fromSexp d with
    | some φ, some d => some (.disjIntro2 φ d)
    | _, _ => none
  | .node [.atom "disjElim", d, dL, dR] =>
    match fromSexp d, fromSexp dL, fromSexp dR with
    | some d, some dL, some dR => some (.disjElim d dL dR)
    | _, _, _ => none
  | .node [.atom "flsElim", φ, d] =>
    match DFormula.fromSexp φ, fromSexp d with
    | some φ, some d => some (.flsElim φ d)
    | _, _ => none
  | .node [.atom "allIntro", d] =>
    match fromSexp d with
    | some d => some (.allIntro d)
    | none => none
  | .node [.atom "allElim", t, d] =>
    match DTerm.fromSexp t, fromSexp d with
    | some t, some d => some (.allElim t d)
    | _, _ => none
  | .node [.atom "exIntro", φ, t, d] =>
    match DFormula.fromSexp φ, DTerm.fromSexp t, fromSexp d with
    | some φ, some t, some d => some (.exIntro φ t d)
    | _, _, _ => none
  | .node [.atom "exElim", ψ, d, dBody] =>
    match DFormula.fromSexp ψ, fromSexp d, fromSexp dBody with
    | some ψ, some d, some dBody => some (.exElim ψ d dBody)
    | _, _, _ => none
  | .node [.atom "emPosit", φ] =>
    match DFormula.fromSexp φ with
    | some φ => some (.emPosit φ)
    | none => none
  | .node [.atom "lpoPosit", φ] =>
    match DFormula.fromSexp φ with
    | some φ => some (.lpoPosit φ)
    | none => none
  | .node [.atom "mpPosit", φ] =>
    match DFormula.fromSexp φ with
    | some φ => some (.mpPosit φ)
    | none => none
  | _ => none

/-- The derivation codec is lossless for EVERY derivation tree: the
Phase-2 completeness theorem. No rule of the kernel can be dropped,
renamed, or permuted by the wire format without this proof breaking. -/
theorem fromSexp_toSexp (d : Deriv) : fromSexp d.toSexp = some d := by
  induction d <;>
    simp [toSexp, fromSexp, natFromSexp_toSexp,
          DTerm.fromSexp_toSexp, DFormula.fromSexp_toSexp, *]

end Deriv

/-! ## Ledgers, contexts, verdicts, jobs -/

namespace Ledger

/-- Encode the posit-and-tier ledger: `(ledger em lpo mp indFull)`. -/
def toSexp (l : Ledger) : Sexp :=
  .node [.atom "ledger", boolToSexp l.em, boolToSexp l.lpo,
         boolToSexp l.mp, boolToSexp l.indFull]

/-- Decode a ledger. -/
def fromSexp : Sexp → Option Ledger
  | .node [.atom "ledger", e, l, m, i] =>
    match boolFromSexp e, boolFromSexp l, boolFromSexp m, boolFromSexp i with
    | some e, some l, some m, some i => some ⟨e, l, m, i⟩
    | _, _, _, _ => none
  | _ => none

theorem fromSexp_toSexp (l : Ledger) : fromSexp l.toSexp = some l := by
  cases l with
  | mk e lp m i => cases e <;> cases lp <;> cases m <;> cases i <;> rfl

end Ledger

/-- Encode a context: `(ctx φ₁ ... φₙ)`. -/
def ctxToSexp (Γ : Ctx) : Sexp :=
  .node (.atom "ctx" :: Γ.map DFormula.toSexp)

/-- Decode a list of formulas. -/
def formulasFromSexp : List Sexp → Option (List DFormula)
  | [] => some []
  | e :: es =>
    match DFormula.fromSexp e, formulasFromSexp es with
    | some φ, some φs => some (φ :: φs)
    | _, _ => none

/-- Decode a context. -/
def ctxFromSexp : Sexp → Option Ctx
  | .node (.atom "ctx" :: es) => formulasFromSexp es
  | _ => none

theorem ctxFromSexp_toSexp (Γ : Ctx) : ctxFromSexp (ctxToSexp Γ) = some Γ := by
  suffices h : formulasFromSexp (Γ.map DFormula.toSexp) = some Γ by
    simp [ctxToSexp, ctxFromSexp, h]
  induction Γ with
  | nil => rfl
  | cons φ Γ ih => simp [List.map, formulasFromSexp, DFormula.fromSexp_toSexp, ih]

/-- Encode a check verdict: `(ok φ ledger)` or `(reject)`. -/
def verdictToSexp : Option (DFormula × Ledger) → Sexp
  | none => .node [.atom "reject"]
  | some (φ, l) => .node [.atom "ok", φ.toSexp, l.toSexp]

/-- Decode a verdict. -/
def verdictFromSexp : Sexp → Option (Option (DFormula × Ledger))
  | .node [.atom "reject"] => some none
  | .node [.atom "ok", φ, l] =>
    match DFormula.fromSexp φ, Ledger.fromSexp l with
    | some φ, some l => some (some (φ, l))
    | _, _ => none
  | _ => none

theorem verdictFromSexp_toSexp (v : Option (DFormula × Ledger)) :
    verdictFromSexp (verdictToSexp v) = some v := by
  match v with
  | none => rfl
  | some (φ, l) =>
    simp [verdictToSexp, verdictFromSexp,
          DFormula.fromSexp_toSexp, Ledger.fromSexp_toSexp]

/-- Encode a checking job: `(job (ctx ...) deriv)`. -/
def jobToSexp (Γ : Ctx) (d : Deriv) : Sexp :=
  .node [.atom "job", ctxToSexp Γ, d.toSexp]

/-- Decode a checking job. -/
def jobFromSexp : Sexp → Option (Ctx × Deriv)
  | .node [.atom "job", Γ, d] =>
    match ctxFromSexp Γ, Deriv.fromSexp d with
    | some Γ, some d => some (Γ, d)
    | _, _ => none
  | _ => none

theorem jobFromSexp_toSexp (Γ : Ctx) (d : Deriv) :
    jobFromSexp (jobToSexp Γ d) = some (Γ, d) := by
  simp [jobToSexp, jobFromSexp, ctxFromSexp_toSexp, Deriv.fromSexp_toSexp]

/-! ## The end-to-end wire pipeline -/

/-- Run a job S-expression through the kernel: decode, `check`, encode the
verdict. `none` means the INPUT was malformed (distinct from `(reject)`,
which means the derivation tree was well-formed data the kernel refused). -/
def checkJobSexp (e : Sexp) : Option Sexp :=
  match jobFromSexp e with
  | some (Γ, d) => some (verdictToSexp (check Γ d))
  | none => none

/-- Decode-then-check agrees with direct checking on every job: the wire
pipeline neither weakens nor strengthens the kernel. This composes the
codec completeness theorems with `check`; it is the theorem the
differential harness is an empirical shadow of. -/
theorem checkJobSexp_complete (Γ : Ctx) (d : Deriv) :
    checkJobSexp (jobToSexp Γ d) = some (verdictToSexp (check Γ d)) := by
  simp [checkJobSexp, jobFromSexp_toSexp]

/-- String-level entry point for the binary: parse, decode, check, print.
Errors are S-expressions too, so the output is always machine-readable. -/
def runJob (s : String) : String :=
  match Sexp.parse s with
  | none => "(error parse)"
  | some e =>
    match checkJobSexp e with
    | none => "(error malformed-job)"
    | some v => v.print

end DeltaKernel
end IndisputableMonolith
