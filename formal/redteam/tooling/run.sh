#!/usr/bin/env bash
# Red-team regression for the tooling checks (formal/work/trust/tooling.md):
#   scripts/Axioms.lean (axiom policy + MetaScan), scripts/lint.py, and leanchecker.
#
#   formal/redteam/tooling/run.sh            # all fixtures
#   formal/redteam/tooling/run.sh Fake Sorry # selected fixtures
#
# Each fixture in RT/ imports only Init/Lean, is compiled into a temporary directory (never into
# .lake/), and every checker's verdict is compared with the expectation table below. A fixture
# that a checker is NOT expected to catch is listed as `miss` on purpose: that is the documented
# coverage gap that another checker closes (e.g. RunTac: MetaScan misses, leanchecker catches).
# Exit code 1 if any verdict differs from the table.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
FORMAL=$(cd "$HERE/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"
# Python never imports from the working directory or the script directory (trust2.opus N2/N3):
# every call uses -I; PYTHONSAFEPATH covers any call that might lack it.
export PYTHONSAFEPATH=1 PYTHONDONTWRITEBYTECODE=1
OUT=$(mktemp -d)
mkdir -p "$OUT/RT"
trap 'rm -rf "$OUT"' EXIT

# fixture      Axioms(dev)  Axioms(--no-sorry)  lint(dev)  lint(--release)  leanchecker
TABLE="
CmdElab        catch        catch               catch      catch            miss
TermElab       catch        catch               catch      catch            miss
PrintAxioms    catch        catch               catch      catch            miss
MacroRules     catch        catch               catch      catch            miss
ModHook        catch        catch               catch      catch            miss
Bypass         catch        catch               catch      catch            catch
RunTac         miss         miss                catch      catch            catch
Init           catch        catch               catch      catch            miss
CSimp          catch        catch               catch      catch            miss
Fake           catch        catch               catch      catch            miss
Notation       catch        catch               catch      catch            miss
Axiom          catch        catch               catch      catch            miss
Sorry          miss         catch               miss       catch            miss
Benign         miss         miss                miss       miss             miss
"

verdict() { if [ "$1" -eq 0 ]; then echo miss; else echo catch; fi; }
fail=0
cd "$HERE"
while read -r name ax axns li lirel lc; do
  [ -z "$name" ] && continue
  if [ $# -gt 0 ] && ! printf '%s\n' "$@" | grep -qx "$name"; then continue; fi
  src="RT/$name.lean"
  if ! lean --root=. -o "$OUT/RT/$name.olean" "$src" > "$OUT/$name.compile.log" 2>&1; then
    echo "FAIL $name: fixture does not compile"; sed 's/^/    /' "$OUT/$name.compile.log" | head -20; fail=1; continue
  fi
  LEAN_PATH="$OUT" lean --run "$FORMAL/scripts/Axioms.lean" --prefix RT --prefix Erdos184 "RT.$name" > "$OUT/$name.ax" 2>&1
  g_ax=$(verdict $?)
  LEAN_PATH="$OUT" lean --run "$FORMAL/scripts/Axioms.lean" --no-sorry --prefix RT --prefix Erdos184 "RT.$name" > "$OUT/$name.axns" 2>&1
  g_axns=$(verdict $?)
  python3 -I "$FORMAL/scripts/lint.py" "$HERE/$src" > "$OUT/$name.lint" 2>&1
  g_li=$(verdict $?)
  python3 -I "$FORMAL/scripts/lint.py" --release "$HERE/$src" > "$OUT/$name.lintrel" 2>&1
  g_lirel=$(verdict $?)
  LEAN_PATH="$OUT" leanchecker "RT.$name" > "$OUT/$name.lc" 2>&1
  g_lc=$(verdict $?)
  line="$name: Axioms=$g_ax Axioms--no-sorry=$g_axns lint=$g_li lint--release=$g_lirel leanchecker=$g_lc"
  if [ "$ax $axns $li $lirel $lc" = "$g_ax $g_axns $g_li $g_lirel $g_lc" ]; then
    echo "ok   $line"
  else
    echo "FAIL $line (expected Axioms=$ax Axioms--no-sorry=$axns lint=$li lint--release=$lirel leanchecker=$lc)"
    for f in ax axns lint lintrel lc; do sed "s/^/    [$f] /" "$OUT/$name.$f" | grep -v "^    \[$f\] SORRY" | head -8; done
    fail=1
  fi
done <<< "$TABLE"
[ "$fail" = 0 ] && echo "redteam/tooling: all verdicts as expected" || echo "redteam/tooling: UNEXPECTED VERDICTS"
exit $fail
