#!/usr/bin/env bash
# Verify the Recognition Science front door (IndisputableMonolith/Verdict.lean).
#
# Run on the build box from the repo root:
#   bash scripts/verify_rs.sh [out.html]
#
# Steps (each prints PASS/FAIL; exit code is nonzero on any FAIL):
#   1. lake build IndisputableMonolith.Verdict
#   2. #print axioms for every Verdict theorem == [propext, Classical.choice, Quot.sound]
#   3. scripts/verdict_audit.lean: transitive closure of the front-door theorem;
#      no AXIOM line, no never-elaborated module (UnifiedReality), no physics
#      application module (Gravity/Cosmology/Masses/Particle), every def documented
#   4. token scan of every source file in the closure: no sorry, axiom, native_decide,
#      implemented_by, unsafe, partial
#   5. HTML report: every definition and structure in the closure with its docstring
set -u
cd "$(dirname "$0")/.."
source ~/.elan/env 2>/dev/null || true
OUT="${1:-plans/RS_Verdict_Report_$(date +%Y%m%d).html}"
TMP="$(mktemp -d)"
FAIL=0
pass() { echo "PASS  $1"; }
fail() { echo "FAIL  $1"; FAIL=1; }

# 1. build
if lake build IndisputableMonolith.Verdict >"$TMP/build.log" 2>&1; then
  pass "lake build IndisputableMonolith.Verdict"
else
  fail "lake build IndisputableMonolith.Verdict (see $TMP/build.log)"
  tail -30 "$TMP/build.log"
  exit 1
fi

# 2. axioms
THMS="recognition_science cost_of_premises dep_forces_three kept_iff_linking premises_consistent kept_independent conclusions_need_kept kept_is_not_distinctness decoys"
{
  echo "import IndisputableMonolith.Verdict"
  for t in $THMS; do echo "#print axioms IndisputableMonolith.Verdict.$t"; done
} >"$TMP/axioms.lean"
lake env lean "$TMP/axioms.lean" >"$TMP/axioms.txt" 2>&1
AXOK=1
for t in $THMS; do
  line=$(grep -E "Verdict\.$t' (depends on axioms|does not depend)" "$TMP/axioms.txt" | head -1)
  if [ -z "$line" ]; then AXOK=0; echo "      $t: no #print axioms line"; continue; fi
  case "$line" in
    *"does not depend on any axioms"*) ;;
    *)
      axs=$(echo "$line" | sed -E 's/.*\[(.*)\].*/\1/' | tr ',' '\n' | tr -d ' ')
      for a in $axs; do
        case "$a" in propext|Classical.choice|Quot.sound) ;; *) AXOK=0; echo "      $t: extra axiom $a" ;; esac
      done ;;
  esac
done
[ $AXOK = 1 ] && pass "#print axioms: every Verdict theorem rests on [propext, Classical.choice, Quot.sound] only" \
              || fail "#print axioms: unexpected axiom set above"

# 3. closure audit
lake env lean scripts/verdict_audit.lean >"$TMP/audit.tsv" 2>"$TMP/audit.err"
if [ -s "$TMP/audit.err" ]; then fail "verdict_audit.lean did not run cleanly"; cat "$TMP/audit.err" | head -20; fi
grep -v '^REACH' "$TMP/audit.tsv" >"$TMP/closure.tsv"
N_AX=$(awk -F'\t' '$1=="AXIOM"' "$TMP/closure.tsv" | wc -l | tr -d ' ')
[ "$N_AX" = 0 ] && pass "closure: 0 axiom declarations of ours" || { fail "closure: $N_AX axiom declarations"; awk -F'\t' '$1=="AXIOM"' "$TMP/closure.tsv"; }
N_UR=$(grep -c 'UnifiedReality' "$TMP/closure.tsv" || true)
[ "$N_UR" = 0 ] && pass "closure: no never-elaborated module" || fail "closure: $N_UR constants from UnifiedReality"
N_REACH=$(grep -c '^REACH' "$TMP/audit.tsv" || true)
[ "$N_REACH" = 0 ] && pass "closure: no physics-application module (Gravity/Cosmology/Masses/Particle)" \
                   || { fail "closure: $N_REACH constants from physics-application modules"; grep '^REACH' "$TMP/audit.tsv" | cut -f2,5 | head; }
for bad in RecognitionKernelV2 SpatialDualPairRealization SupportsNontrivialLinking; do
  n=$(cut -f2 "$TMP/closure.tsv" | grep -c "$bad" || true)
  [ "$n" = 0 ] && pass "closure: no $bad" || fail "closure: $n constants named $bad"
done
N_UNDOC=$(awk -F'\t' '($1=="def"||$1=="structure"||$1=="inductive") && $4==""' "$TMP/closure.tsv" | wc -l | tr -d ' ')
[ "$N_UNDOC" = 0 ] && pass "closure: every definition and structure carries a docstring" \
                   || { fail "closure: $N_UNDOC undocumented definitions"; awk -F'\t' '($1=="def"||$1=="structure"||$1=="inductive") && $4==""' "$TMP/closure.tsv" | cut -f2; }

# 4. token scan over closure source files
cut -f3 "$TMP/closure.tsv" | sort -u | grep '^IndisputableMonolith' | sed 's#\.#/#g; s#$#.lean#' >"$TMP/files.txt"
N_FILES=$(wc -l <"$TMP/files.txt" | tr -d ' ')
TOK=0
python3 - "$TMP/files.txt" <<'PY' || TOK=1
import re, sys
files = [l.strip() for l in open(sys.argv[1]) if l.strip()]
bad = 0
def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and src.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if src[i] == "\n" else " "); i += 1; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        out.append(src[i]); i += 1
    return "".join(out)
pat = re.compile(r"^\s*(axiom|unsafe|partial)\b|\bsorry\b|\bnative_decide\b|implemented_by|\bextern\b", re.M)
for f in files:
    try:
        code = strip_comments(open(f, encoding="utf-8").read())
    except FileNotFoundError:
        print(f"      missing {f}"); bad += 1; continue
    for m in pat.finditer(code):
        line = code.count("\n", 0, m.start()) + 1
        print(f"      {f}:{line}: {code[m.start():m.start()+60].splitlines()[0]}"); bad += 1
sys.exit(1 if bad else 0)
PY
[ $TOK = 0 ] && pass "token scan over $N_FILES closure source files: no sorry/axiom/native_decide/implemented_by/unsafe/partial" \
             || fail "token scan: suspicious tokens above"

# 5. report
python3 - "$TMP/closure.tsv" "$TMP/axioms.txt" "$OUT" "$FAIL" "$N_FILES" <<'PY'
import sys, html, collections
tsv, axf, out, failed, nfiles = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4] == "1", sys.argv[5]
rows = [l.rstrip("\n").split("\t") for l in open(tsv) if l.strip()]
rows = [r + [""] * (4 - len(r)) for r in rows]
kinds = collections.Counter(r[0] for r in rows)
mods = collections.Counter(r[2] for r in rows)
ax = open(axf).read()
def esc(s): return html.escape(s)
verdict_first = sorted(rows, key=lambda r: (0 if r[2] == "IndisputableMonolith.Verdict" else 1, r[2], r[1]))
h = []
h.append("""<!doctype html><html><head><meta charset="utf-8"><title>RS Verdict report</title>
<style>body{font-family:Georgia,serif;max-width:1100px;margin:2rem auto;padding:0 1rem;color:#111;line-height:1.45}
h1,h2{font-family:Helvetica,Arial,sans-serif;letter-spacing:-.01em}code,pre{font-family:Menlo,Consolas,monospace;font-size:.86em}
pre{background:#f5f5f2;padding:.8rem;border:1px solid #ddd;overflow:auto}table{border-collapse:collapse;width:100%;font-size:.9em}
td,th{border-top:1px solid #ddd;padding:.35rem .5rem;vertical-align:top;text-align:left}th{background:#f0f0ea}
.k{white-space:nowrap;color:#555}.pass{color:#0a6b1f;font-weight:bold}.fail{color:#a11;font-weight:bold}.m{color:#777;font-size:.85em}</style></head><body>""")
h.append("<h1>Recognition Science: Verdict report</h1>")
h.append(f"<p class='{'fail' if failed else 'pass'}'>{'SOME CHECKS FAILED' if failed else 'All checks passed'}.</p>")
h.append("<p>Generated by <code>scripts/verify_rs.sh</code>. Front door: <code>IndisputableMonolith/Verdict.lean</code>, theorem <code>recognition_science</code>.</p>")
h.append("<h2>Axioms</h2><pre>" + esc(ax) + "</pre>")
h.append(f"<h2>Closure</h2><p>{len(rows)} constants of ours in the transitive closure of the front door, across {len(mods)} modules ({nfiles} source files). "
         + ", ".join(f"{k}: {v}" for k, v in sorted(kinds.items())) + ".</p>")
h.append("<table><tr><th>module</th><th>constants</th></tr>" + "".join(f"<tr><td><code>{esc(m)}</code></td><td>{n}</td></tr>" for m, n in sorted(mods.items(), key=lambda x: -x[1])) + "</table>")
h.append("<h2>Every definition and structure the theorem depends on</h2><p>Read each docstring and decide whether the definition means what its words say. Theorems are listed after; their statements are checked by the kernel.</p>")
h.append("<table><tr><th>kind</th><th>name</th><th>meaning</th></tr>")
for r in verdict_first:
    if r[0] in ("def", "structure", "inductive", "opaque"):
        h.append(f"<tr><td class='k'>{esc(r[0])}</td><td><code>{esc(r[1].replace('IndisputableMonolith.', ''))}</code><div class='m'>{esc(r[2].replace('IndisputableMonolith.', ''))}</div></td><td>{esc(r[3]) or '<span class=fail>(no docstring)</span>'}</td></tr>")
h.append("</table><h2>Theorems in the closure</h2><table><tr><th>name</th><th>statement in words</th></tr>")
for r in verdict_first:
    if r[0] == "theorem":
        h.append(f"<tr><td><code>{esc(r[1].replace('IndisputableMonolith.', ''))}</code><div class='m'>{esc(r[2].replace('IndisputableMonolith.', ''))}</div></td><td>{esc(r[3])}</td></tr>")
h.append("</table></body></html>")
open(out, "w").write("\n".join(h))
print(f"report: {out}")
PY

echo
[ $FAIL = 0 ] && echo "VERDICT CHECKS: ALL PASS" || echo "VERDICT CHECKS: FAIL"
exit $FAIL
