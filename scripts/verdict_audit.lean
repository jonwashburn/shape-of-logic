/-
Verdict audit: list every constant the front-door theorem depends on inside the
IndisputableMonolith namespace, with its kind, defining module, and docstring.

Run (on the build box, from the repo root):
  lake env lean scripts/verdict_audit.lean > /tmp/verdict_audit.tsv

Output: tab-separated lines  KIND \t NAME \t MODULE \t DOCSTRING(one line)
KIND ∈ {AXIOM, def, opaque, inductive, structure, theorem}. Auto-generated names
(proof terms, match compilers, equation lemmas, instances, private names) are skipped.
A line beginning with AXIOM anywhere in the output is a failure.
-/
import IndisputableMonolith.Verdict

open Lean Meta

namespace VerdictAudit

/-- Modules a reader would not expect in the kernel closure; every constant found in
one of them is reported with the constant that first reached it. -/
def suspectModules : List String := ["Gravity", "Cosmology", "Masses", "Particle", "Chemistry"]

partial def collect (env : Environment) (visited : IO.Ref NameSet) (parent : Name) (n : Name) :
    IO Unit := do
  if (← visited.get).contains n then return
  visited.modify (·.insert n)
  if (`IndisputableMonolith).isPrefixOf n then
    match env.getModuleFor? n with
    | some m =>
      if suspectModules.any (fun s => (m.toString.splitOn s).length > 1) then
        IO.eprintln s!"REACH\t{n}\t{m}\tvia\t{parent}"
    | none => pure ()
  match env.find? n with
  | none => return
  | some ci =>
    let mut consts := ci.type.getUsedConstants
    match ci.value? with
    | some v => consts := consts ++ v.getUsedConstants
    | none => pure ()
    match ci with
    | .inductInfo iv => consts := consts ++ iv.ctors.toArray
    | _ => pure ()
    for c in consts do
      collect env visited n c

def generatedMarkers : List String :=
  ["._", ".proof_", ".match_", ".eq_", "._private", ".inst", ".rec", ".casesOn",
   ".noConfusion", ".mk", ".injEq", ".sizeOf", ".below", ".brecOn", ".ibelow",
   ".binductionOn", ".ctorIdx", ".toCtorIdx"]

def isGenerated (n : Name) : Bool :=
  let s := n.toString
  n.isInternal || generatedMarkers.any (fun m => (s.splitOn m).length > 1)

def oneLine (s : String) : String :=
  (s.replace "\n" " ").replace "\t" " "

def run : MetaM Unit := do
  let env ← getEnv
  let visited ← IO.mkRef ({} : NameSet)
  for root in [``IndisputableMonolith.Verdict.recognition_science,
      ``IndisputableMonolith.Verdict.premises_consistent,
      ``IndisputableMonolith.Verdict.kept_independent,
      ``IndisputableMonolith.Verdict.kept_iff_linking,
      ``IndisputableMonolith.Verdict.conclusions_need_kept,
      ``IndisputableMonolith.Verdict.kept_is_not_distinctness,
      ``IndisputableMonolith.Verdict.decoys] do
    collect env visited .anonymous root
  let names := (← visited.get).toList.filter fun n =>
    (`IndisputableMonolith).isPrefixOf n && !isGenerated n
  let sorted := names.toArray.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    let some ci := env.find? n | continue
    let kind : String := match ci with
      | .axiomInfo _ => "AXIOM"
      | .defnInfo _ => "def"
      | .opaqueInfo _ => "opaque"
      | .thmInfo _ => "theorem"
      | .inductInfo iv => if isStructure env iv.name then "structure" else "inductive"
      | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec"
      | .quotInfo _ => "quot"
    if kind == "ctor" || kind == "rec" || kind == "quot" then continue
    -- structure projections are defs; report them under their structure instead
    if kind == "def" then
      if let some _ := env.getProjectionFnInfo? n then continue
    let modName : String := match env.getModuleFor? n with
      | some m => m.toString
      | none => "?"
    let doc ← findDocString? env n
    let docStr := match doc with
      | some d => oneLine d
      | none => ""
    IO.println s!"{kind}\t{n}\t{modName}\t{docStr}"

end VerdictAudit

#eval VerdictAudit.run
