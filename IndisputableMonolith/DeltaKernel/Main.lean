import IndisputableMonolith.DeltaKernel.Corpus

/-!
# `deltak`: the extracted δ-kernel checker (Phase 2)

A standalone binary wrapping the SAME `check` function the machine-checked
soundness theorem (`Sound.lean`) is about. Not a from-scratch prover: the
panel killed the C-binary-first path because rebuilding parsing and
elaboration buys zero foundational content and relocates trust to a
compiler. Here the trust story is explicit:

- the kernel logic (`check`) is compiled from the exact Lean definition the
  soundness proof covers;
- the wire codec's losslessness is a THEOREM (`Serialize.lean`), checked by
  Lean's kernel over all derivations;
- what the compiler adds is validated DIFFERENTIALLY: `deltak selftest`
  re-evaluates the golden corpus with compiled code and compares against
  verdicts Lean's kernel froze by `decide` (`Corpus.lean`). The binary is
  never the sole authority; disagreement with the Lean-hosted verdicts is
  a hard failure.

Commands:
- `deltak check <file|->`   check a `(job (ctx ...) <deriv>)` S-expression,
                            print `(ok φ (ledger em lpo mp indFull))` or
                            `(reject)`.
- `deltak emit [dir]`       write the golden corpus as `<name>.job` /
                            `<name>.expected` files (default `deltak_corpus/`).
- `deltak selftest`         differential validation: compiled check vs
                            kernel-frozen verdicts, plus string-level
                            round-trip of every corpus job. Exit 0 iff all
                            pass.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- Render a verdict for humans AND machines: the S-expression is the
machine layer; the trailing comment names the verdict class. -/
def describeVerdict (v : Option (DFormula × Ledger)) : String :=
  match v with
  | none => "(reject)"
  | some (φ, l) =>
    let cls :=
      if l = Ledger.empty then "FORCED"
      else if l = Ledger.ofIndFull then "FORCED @ FULL-IND"
      else "CONDITIONAL"
    s!"{(verdictToSexp (some (φ, l))).print}  ; {cls}"

/-- One selftest line: differential check + string round-trip for an entry. -/
def selftestEntry (e : CorpusEntry) : Bool × String :=
  -- Differential leg: compiled `check` vs the kernel-frozen literal.
  let got := check e.ctx e.deriv
  let diffOk := got == e.expected
  -- Wire leg: print → parse → decode → re-check must reproduce the verdict.
  let jobStr := (jobToSexp e.ctx e.deriv).print
  let wireOk :=
    match Sexp.parse jobStr with
    | none => false
    | some sexp =>
      match jobFromSexp sexp with
      | none => false
      | some (Γ, d) => check Γ d == e.expected
  let ok := diffOk && wireOk
  let tag := if ok then "PASS" else
    (if diffOk then "FAIL[wire]" else "FAIL[diff]")
  (ok, s!"{tag}  {e.name}: {describeVerdict got}")

/-- Run the full selftest; returns `(allPassed, report lines)`. -/
def runSelftest : Bool × List String :=
  let results := corpus.map selftestEntry
  (results.all (·.1), results.map (·.2))

end DeltaKernel
end IndisputableMonolith

open IndisputableMonolith.DeltaKernel

def cmdCheck (path : String) : IO UInt32 := do
  let input ← if path = "-" then (← IO.getStdin).readToEnd
              else IO.FS.readFile path
  let out := runJob input
  IO.println out
  pure (if out.startsWith "(error" then 2 else 0)

def cmdEmit (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  for e in corpus do
    IO.FS.writeFile s!"{dir}/{e.name}.job" ((jobToSexp e.ctx e.deriv).print ++ "\n")
    IO.FS.writeFile s!"{dir}/{e.name}.expected" ((verdictToSexp e.expected).print ++ "\n")
  IO.println s!"emitted {corpus.length} jobs to {dir}/"
  pure 0

def cmdSelftest : IO UInt32 := do
  let (ok, lines) := runSelftest
  for l in lines do IO.println l
  if ok then
    IO.println s!"selftest: all {corpus.length} entries agree with the Lean-frozen verdicts"
    pure 0
  else
    IO.println "selftest: DISAGREEMENT with the Lean-hosted kernel; do not trust this binary"
    pure 1

def usage : String :=
  "deltak: extracted δ-kernel checker (differentially validated against Lean)\n" ++
  "usage:\n" ++
  "  deltak check <file|->   check a (job ...) S-expression\n" ++
  "  deltak emit [dir]       write the golden corpus (default deltak_corpus/)\n" ++
  "  deltak selftest         compiled check vs Lean-frozen verdicts + wire round-trip"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check", path] => cmdCheck path
  | ["emit"] => cmdEmit "deltak_corpus"
  | ["emit", dir] => cmdEmit dir
  | ["selftest"] => cmdSelftest
  | _ => IO.println usage; pure 64
